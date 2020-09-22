# Copyright 2020 SciresM
#
# Permission to use, copy, modify, and/or distribute this software for any purpose
# with or without fee is hereby granted, provided that the above copyright notice
# and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
# FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT,
# OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE,
# DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS
# ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

from unicorn import *
from unicorn.arm64_const import *
import math, os, re, struct, sys
from struct import unpack as up, pack as pk
from io import BytesIO
import idaapi
import idc
import ida_struct

if sys.version_info[0] == 3:
    iter_range = range
    int_types = (int,)
    ascii_string = lambda b: b.decode('ascii')
    bytes_to_list = lambda b: list(b)
    list_to_bytes = lambda l: bytes(l)
else:
    iter_range = xrange
    int_types = (int, long)
    ascii_string = lambda b: str(b)
    bytes_to_list = lambda b: map(ord, b)
    list_to_bytes = lambda l: ''.join(map(chr, l))

IRAM_BASE    = 0x40000000
IRAM_SIZE    = 0x00040000
DRAM_BASE    = 0x80000000
DRAM_SIZE    = 0x00020000
PK1L_ADDRESS = 0x40010000
PK1L_SIZE    = IRAM_BASE + IRAM_SIZE - PK1L_ADDRESS

TZRAM_BASE   = 0x7C010000
TZRAM_SIZE   = 0x00040000

KNOWN_MAPPINGS = {
    (0x50041000, 0x1000) : ('.arm_gicd',    'IO'),
    (0x50042000, 0x2000) : ('.arm_gicc',    'IO'),
    (0x70006000, 0x1000) : ('.uart',        'IO'),
    (0x60006000, 0x1000) : ('.clkrst',      'IO'),
    (0x7000e000, 0x1000) : ('.rtcpmc',      'IO'),
    (0x60005000, 0x1000) : ('.timers',      'IO'),
    (0x6000c000, 0x1000) : ('.system',      'IO'),
    (0x70012000, 0x2000) : ('.se',          'IO'),
    (0x700f0000, 0x1000) : ('.sysctr0',     'IO'),
    (0x70019000, 0x1000) : ('.mc',          'IO'),
    (0x7000f000, 0x1000) : ('.fuses',       'IO'),
    (0x70000000, 0x4000) : ('.misc',        'IO'),
    (0x60007000, 0x1000) : ('.flow',        'IO'),
    (0x7000d000, 0x1000) : ('.i2c5',        'IO'),
    (0x6000d000, 0x1000) : ('.gpio1',       'IO'),
    (0x7000c000, 0x1000) : ('.i2c1',        'IO'),
    (0x6000f000, 0x1000) : ('.evp',         'IO'),
    (0x7001c000, 0x1000) : ('.mc0',         'IO'),
    (0x7001d000, 0x1000) : ('.mc1',         'IO'),
    (0x70412000, 0x2000) : ('.se2',         'IO'),
}

def find_entrypoint(data):
    if data[0x4000:0x4004] == 'PK11':
        ofs = 0x4000
    elif data[0x7000:0x7004] == 'PK11':
        ofs = 0x7000
    elif data[0x7170:0x7174] == 'PK11':
        ofs = 0x7170
    else:
        raise ValueError('No PK11 Header?')
    for i in xrange(4, 0x20, 4):
        semo_maybe = ofs + 0x20 + up('<I', data[ofs + i:ofs + i + 4])[0]
        if 4 <= semo_maybe and semo_maybe <= len(data) - 4:
            if data[semo_maybe-4:semo_maybe+4] == '\x00\x00\x00\x00\xDF\x4F\x03\xD5':
                return semo_maybe
    raise ValueError('Failed to find SecMon')

class Emulator:
    REGISTER_IDS = [UC_ARM64_REG_X0 + i for i in xrange(29)] + [UC_ARM64_REG_X29, UC_ARM64_REG_X30]

    def __init__(self):
        self.modified_instructions = []
        self.tracked_reads = []
        self.calling_function = False
        self.function_calls = {}
        self.virt_to_phys = {}
        self.phys_to_virt = {}
        self.mappings = []
        self.l3_table = -1
        self.ttbr = -1
        self.vbar = -1
        self.core0_stack_page = -1
        self.smc_lists = []
        self.invalid_instructions = {
            0xD5301180 : 0xD2800000, # msr x0, oslsr_el1 -> mov x0, #0x0
            0xD50E831F : 0xD503201F  # TLBI ALLE3IS -> nop
        }
        for i in xrange(31):
            self.invalid_instructions[0xD51E1100 + i] = 0xD503201F     # scr_el3   -> nop
            self.invalid_instructions[0xD51E1140 + i] = 0xD503201F     # cptr_el3  -> nop
            self.invalid_instructions[0xD51E1140 + i] = 0xD503201F     # cptr_el3  -> nop
            self.invalid_instructions[0xD51E2000 + i] = 0xD503201F     # ttbr0_el3 -> nop
            self.invalid_instructions[0xD51E2040 + i] = 0xD503201F     # tcr_el3   -> nop
            self.invalid_instructions[0xD51EA200 + i] = 0xD503201F     # mair_el3  -> nop
            self.invalid_instructions[0xD51EC000 + i] = 0xD503201F     # vbar_el3  -> nop
            self.invalid_instructions[0xD51E1000 + i] = 0xD503201F     # sctlr_el3 -> nop
        # Initialize emulator in ARM mode
        self.mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)

        # Map in the whole mmio physical address range.
        self.mu.mem_map(0x40000000, 0x40000000)
        self.mu.mem_map(0x80000000, 0x60000)

        self.current_pc = -1
        self.last_invalid_pc = -1

    def patch_instruction(self, uc, address, value):
        old = uc.mem_read(address, len(value))
        self.modified_instructions.append((address, str(old)))
        uc.mem_write(address, value)

    def restore_instructions(self, uc):
        for (addr, val) in self.modified_instructions:
            uc.mem_write(addr, val)
        self.modified_instructions = []

    def add_function_call(self, uc, address):
        if address not in self.function_calls:
            self.function_calls[address] = []
        args = [uc.reg_read(x) for x in [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2, UC_ARM64_REG_X3, UC_ARM64_REG_X4, UC_ARM64_REG_X5, UC_ARM64_REG_X6, UC_ARM64_REG_X7]]
        if args not in self.function_calls[address]:
            self.function_calls[address].append(args)

    def is_mmu_func(self, func):
        calls = self.function_calls[func]
        for c in calls:
            # MMU map function always takes the same L3 table
            if c[0] != calls[0][0]:
                return False
            # MMU map function always maps page aligned vaddr/paddr/size
            if (c[1] & 0xFFF) or (c[2] & 0xFFF) or (c[3] & 0xFFF):
                return False
        # MMU map function maps with consistent attributes
        attrs = set([c[4] for c in calls])
        if not ((0x40000000000304 in attrs) or (0x40000000000324 in attrs) or (0x40000000000004 in attrs)):
            return False
        # MMU always maps the security engine somewhere.
        if len(filter(lambda c: c[2] == 0x70012000 and c[3] >= 0x2000, calls)) == 0:
            return False
        return True

    @staticmethod
    def hook_mem_rw(uc, access, address, size, value, self):
        if access == UC_MEM_READ and self.smc_lists == []:
            sp = uc.reg_read(UC_ARM64_REG_SP)
            if sp <= address and address <= (sp + 0xFFF) & ~0xFFF:
                return
            value = uc.mem_read(address, size)
            value = int(str(value)[::-1].encode('hex'), 16)
            self.tracked_reads.append((address, value))
            if value == 0x84000002:
                expected = (address - 0x20)
                smc_list_reads = filter(lambda x: x[1] == expected, self.tracked_reads)
                assert len(smc_list_reads) == 1
                self.smc_lists_addr = smc_list_reads[0][0] - 0x10
                for i in xrange(2):
                    self.smc_lists.append(up('<QII', uc.mem_read(self.smc_lists_addr + 0x10 * i, 0x10)))

    @staticmethod
    def hook_code_for_smc_handler(uc, address, size, self):
        assert size == 4
        insn = up('<I', uc.mem_read(address, 4))[0]
        self.restore_instructions(uc)
        if (insn & 0xFFFFFFE0) == 0xD53E5200: # esr_el3 access
            self.patch_instruction(uc, address, pk('<I', 0xD503201F))
            uc.reg_write(Emulator.REGISTER_IDS[insn & 0x1F], (0x17 << 26) | (0x1))
        if insn == 0x14000000: # infinite loop
            self.patch_instruction(uc, address, pk('<I', 0xCCCCCCCC))

    @staticmethod
    def hook_code(uc, address, size, self):
        assert size == 4
        insn = up('<I', uc.mem_read(address, 4))[0]
        self.restore_instructions(uc)
        if insn in self.invalid_instructions:
            self.patch_instruction(uc, address, pk('<I', self.invalid_instructions[insn]))
        if self.calling_function:
            self.add_function_call(uc, address)
            self.calling_function = False
        if (insn & 0xFC000000) in [0x94000000]:
            self.calling_function = True
        if (insn & 0xFFFFFFE0) == 0xD51E1000 and len(self.virt_to_phys) == 0:
            mmu_funcs = [func for func in self.function_calls if self.is_mmu_func(func)]
            assert len(mmu_funcs) == 1
            mmu_func = mmu_funcs[0]
            for call in self.function_calls[mmu_func]:
                l3_tab, vaddr, paddr, size, attr = tuple(call[:5])
                self.l3_table = l3_tab
                if vaddr != paddr:
                    assert vaddr >= 0x80000000
                    uc.mem_map(vaddr, size)
                    mem = uc.mem_read(paddr, size)
                    uc.mem_write(vaddr, str(mem))
                    self.virt_to_phys[vaddr] = (paddr, size, attr)
                    self.phys_to_virt[paddr] = (vaddr, size, attr)
                    self.mappings.append((vaddr, paddr, size, attr))
        if (insn & 0xFFFFFFE0) == 0xD51EC000:
            # VBAR set
            which = insn & 0x1F
            self.vbar = uc.reg_read(Emulator.REGISTER_IDS[which])
        if (insn & 0xFFFFFFE0) == 0xD51E2000:
            # TTBR set
            which = insn & 0x1F
            self.ttbr = uc.reg_read(Emulator.REGISTER_IDS[which])
            assert (self.ttbr & 0x7FF) == 0x7C0

    def read_mem(self, addr, size):
        return str(self.mu.mem_read(addr, size))

    def simulate(self, pc, steps):
        self.current_pc = pc
        while True:
            try:
                self.mu.emu_start(self.current_pc, 0xFFFFFFFFFFFFFFFF, 0, steps)
                break
            except UcError as e:
                self.current_pc = self.mu.reg_read(UC_ARM64_REG_PC)
                if e.errno == UC_ERR_EXCEPTION:
                    if self.current_pc == self.last_invalid_pc:
                        break
                    else:
                        self.last_invalid_pc = self.current_pc
                        continue
                break

    def run_emulator(self, data):
        self.mu.mem_write(PK1L_ADDRESS, data)
        entrypoint = PK1L_ADDRESS + find_entrypoint(data)
        h = self.mu.hook_add(UC_HOOK_CODE, Emulator.hook_code, self)
        if entrypoint == PK1L_ADDRESS + 0x20170:
            data = data[:0x20000] + data[0x20170:]
            entrypoint = PK1L_ADDRESS + 0x20000
        self.mu.mem_write(PK1L_ADDRESS, data)

        self.entrypoint = entrypoint
        self.simulate(entrypoint, 1500000)
        #with open('C:/dev/debug.bin', 'wb') as f:
        #    f.write(self.mu.mem_read(0x40030000, 0x10000))
        #    f.write(self.mu.mem_read(0x7C010000, 0x10000))
        assert self.vbar != -1
        assert self.ttbr != -1
        if self.l3_table == -1:
            self.found_smc_evp = False
            return
        self.found_smc_evp = True
        assert self.l3_table != -1

        # Remove previous hook, setup to invoke smc_cpu_off
        self.mu.hook_del(h)
        h  = self.mu.hook_add(UC_HOOK_CODE,     Emulator.hook_code_for_smc_handler, self)
        h2 = self.mu.hook_add(UC_HOOK_MEM_READ, Emulator.hook_mem_rw, self)
        self.mu.reg_write(UC_ARM64_REG_X0, 0x84000002)
        self.mu.reg_write(UC_ARM64_REG_X1, 0)

        # Execute exception handler
        self.simulate(self.vbar + 0x400, 10000)
        self.core0_stack_page = self.mu.reg_read(UC_ARM64_REG_SP) & ~0xFFF
        print '%x' % self.core0_stack_page
        print '%x' % self.l3_table


def accept_file(li, n):
    if not isinstance(n, int_types) or n == 0:
        li.seek(0)
        try:
            find_entrypoint(li.read(PK1L_SIZE))
            return 'NX Secure Monitor'
        except ValueError:
            return 0

def add_segment(start, size, name, kind):
    end = start + size
    idaapi.add_segm(0, start, end, name, kind)
    segm = idaapi.get_segm_by_name(name)
    if kind == 'CONST':
        segm.perm = idaapi.SEGPERM_READ
    elif kind == 'CODE':
        segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_EXEC
    elif kind == 'DATA':
        segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
    elif kind == 'BSS':
        segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
    elif kind == 'IO':
        segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
    elif kind == 'RWX':
        segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_EXEC | idaapi.SEGPERM_WRITE
    idaapi.update_segm(segm)
    idaapi.set_segm_addressing(segm, 2)

def is_tzram(mapping):
    vaddr, paddr, size, attr = mapping
    return TZRAM_BASE <= paddr and paddr < TZRAM_BASE + TZRAM_SIZE

def is_dram(mapping):
    vaddr, paddr, size, attr = mapping
    return DRAM_BASE <= paddr and paddr < DRAM_BASE + DRAM_SIZE

def is_iram(mapping):
    vaddr, paddr, size, attr = mapping
    return IRAM_BASE <= paddr and paddr < IRAM_BASE + IRAM_SIZE

def is_mmio(mapping):
    vaddr, paddr, size, attr = mapping
    return paddr < DRAM_BASE and not (is_tzram(mapping) or is_dram(mapping) or is_iram(mapping))


def add_mmio_mapping(mapping):
    # MMIO
    vaddr, paddr, size, attr = mapping
    assert (paddr, size) in KNOWN_MAPPINGS
    name, kind = KNOWN_MAPPINGS[(paddr, size)]
    add_segment(vaddr, size, name, kind)

def is_executable(mapping):
    return (mapping[3] & 0x0040000000000000) == 0

def is_writable(mapping):
    return (mapping[3] & 0x80) == 0

def load_mapping(emu, mapping):
    vaddr, _, size, _ = mapping
    idaapi.mem2base(emu.read_mem(vaddr, size), vaddr)

def get_smc_name(user, id):
    if user:
        USER_SMCS = {
            0xC3000401 : 'set_config',
            0xC3000002 : 'get_config',
            0xC3000003 : 'get_result',
            0xC3000404 : 'get_result_data',
            0xC3000E05 : 'exp_mod',
            0xC3000006 : 'generate_random_bytes_for_user',
            0xC3000007 : 'generate_aes_kek',
            0xC3000008 : 'load_aes_key',
            0xC3000009 : 'compute_aes',
            0xC300000A : 'generate_specific_aes_key',
            0xC300040B : 'compute_cmac',
            0xC300100C : 'import_es_key',
            0xC300D60C : 'reencrypt_rsa_private_key',
            0xC300100D : 'decrypt_or_import_rsa_key',
            0xC300100E : 'import_lotus_key',
            0xC300060F : 'storage_exp_mod',
            0xC3000610 : 'unwrap_titlekey',
            0xC3000C10 : 'unwrap_titlekey',
            0xC3000011 : 'load_titlekey',
            0xC3000012 : 'unwrap_common_titlekey',
        }
        return USER_SMCS[id]
    else:
        PRIV_SMCS = {
            0xC4000001 : 'cpu_suspend',
            0x84000002 : 'cpu_off',
            0xC4000003 : 'cpu_on',
            0xC3000004 : 'get_config',
            0xC3000005 : 'get_random_bytes_for_privileged',
            0xC3000006 : 'panic',
            0xC3000007 : 'configure_carveout',
            0xC3000008 : 'read_write_register',
        }
        return PRIV_SMCS[id]

def get_disasm(ea):
    return [x.lower() for x in idc.GetDisasm(ea).lstrip().rstrip().replace(', ',' ').split()]

def parse_adr_op(op):
    if op.startswith('unk_'):
        return int(op[4:], 16)
    elif op.startswith('#'):
        return int(op[1:], 0)
    else:
        raise ValueError('Bad ADR operand')

def process_smc(func, smc_name):
    idc.create_insn(func)
    idc.set_name(func, 'smc_%s' % smc_name)
    disasm = get_disasm(func)
    if disasm[:2] == ['adrp', 'x1']:
        d = [get_disasm(ea) for ea in [func, func + 4, func + 8, func + 12, func + 16]]
        if not d[1][:2] == ['adrp', 'x2']:
            return
        if not d[2][:3] == ['add', 'x1', 'x1']:
            return
        if not d[3][:3] == ['add', 'x2', 'x2']:
            return
        if not d[4][0] == 'b':
            return
        func_impl = parse_adr_op(d[0][2]) + parse_adr_op(d[2][3])
        gr_impl   = parse_adr_op(d[1][2]) + parse_adr_op(d[3][3])
        gr_name = '%s_get_result' % smc_name
        if smc_name == 'unwrap_titlekey':
            gr_name += '_data'
        idc.create_insn(func_impl)
        idc.set_name(func_impl, smc_name)
        idc.create_insn(gr_impl)
        idc.set_name(gr_impl, gr_name)
        if d[4][1].startswith('unk_'):
            async_smc = parse_adr_op(d[4][1])
            idc.create_insn(async_smc)
            idc.set_name(async_smc, 'handle_asynchronous_smc')
    elif disasm[:2] == ['adrl', 'x1']:
        branch_d = get_disasm(func + 8)
        if branch_d[0] == 'b':
            func_impl = parse_adr_op(disasm[2])
            idc.create_insn(func_impl)
            idc.set_name(func_impl, smc_name)
            if branch_d[1].startswith('unk_'):
                sync_smc = parse_adr_op(branch_d[1])
                idc.create_insn(sync_smc)
                idc.set_name(sync_smc, 'handle_synchronous_smc')


def load_file(li, neflags, format):
    # Set flags
    idaapi.set_processor_type("arm", idaapi.SETPROC_LOADER_NON_FATAL|idaapi.SETPROC_LOADER)
    idc.set_inf_attr(idc.INF_LFLAGS, idc.get_inf_attr(idc.INF_LFLAGS) | idc.LFLG_64BIT)
    idc.set_inf_attr(idc.INF_DEMNAMES, idaapi.DEMNAM_GCC3)
    idaapi.set_compiler_id(idaapi.COMP_GNU)
    idaapi.add_til('gnulnx_arm64', 1)

    # Load IRAM memory
    li.seek(0)
    pk11 = li.read(PK1L_SIZE)
    idaapi.mem2base(pk11, PK1L_ADDRESS)

    # Add identity mappings
    add_segment(PK1L_ADDRESS, PK1L_SIZE, '.pk1_identity', 'RWX')
    add_segment(TZRAM_BASE, TZRAM_SIZE, '.tz_identity', 'RWX')

    # Emulate package1 to determine interesting extents
    emu = Emulator()
    emu.run_emulator(pk11)

    # Refresh IRAM contents to reflect any decompression that may have occurred.
    idaapi.mem2base(emu.read_mem(PK1L_ADDRESS, PK1L_SIZE), PK1L_ADDRESS)

    if not emu.found_smc_evp:
        # Set coldboot crt0
        idc.create_insn(emu.entrypoint)
        idc.set_name(emu.entrypoint, 'coldboot_crt0')
        return 1

    iram_mappings  = []
    dram_mappings  = []
    tzram_mappings = []
    mmio_mappings  = []

    for m in emu.mappings:
        if is_tzram(m):
            tzram_mappings.append(m)
        elif is_dram(m):
            dram_mappings.append(m)
        elif is_iram(m):
            iram_mappings.append(m)
        else:
            assert is_mmio(m)
            mmio_mappings.append(m)

    for m in mmio_mappings:
        add_mmio_mapping(m)

    # Process IRAM mappings
    if len(iram_mappings) == 3:
        sorted_irams = sorted(iram_mappings, key=lambda m:m[2])
        if [m[2] for m in sorted_irams] == [0x1000, 0x1000, 0x10000]:
            assert len(set([m[3] for m in sorted_irams])) == 2
            if sorted_irams[1][3] == sorted_irams[2][3]:
                add_segment(sorted_irams[0][0], sorted_irams[0][2], '.bl_sync',      'IO')
                add_segment(sorted_irams[1][0], sorted_irams[1][2], '.sc7_fw',       'DATA')
                add_segment(sorted_irams[2][0], sorted_irams[2][2], '.sc7_tmp_save', 'DATA')
            else:
                assert sorted_irams[0][3] == sorted_irams[2][3]
                add_segment(sorted_irams[1][0], sorted_irams[1][2], '.bl_sync',      'IO')
                add_segment(sorted_irams[0][0], sorted_irams[0][2], '.sc7_fw',       'DATA')
                add_segment(sorted_irams[2][0], sorted_irams[2][2], '.sc7_tmp_save', 'DATA')
        else:
            print iram_mappings
            raise ValueError('Unknown IRAM mapping set')
    elif len(iram_mappings) == 2:
        sorted_irams = sorted(iram_mappings, key=lambda m:m[2])
        if [m[2] for m in sorted_irams] == [0x1000, 0x10000]:
            assert len(set([m[3] for m in sorted_irams])) == 2
            add_segment(sorted_irams[0][0], sorted_irams[0][2], '.bl_sync',      'IO')
            add_segment(sorted_irams[1][0], sorted_irams[1][2], '.sc7_tmp_save', 'DATA')
        else:
            print iram_mappings
            raise ValueError('Unknown IRAM mapping set')
    else:
        print iram_mappings
        raise ValueError('Unknown IRAM mapping set')

    # Process DRAM mappings
    if len(dram_mappings) == 2:
        sorted_drams = sorted(dram_mappings, key=lambda m:m[2])
        if [m[2] for m in sorted_drams] == [0x1000, 0x10000]:
            add_segment(sorted_drams[0][0], sorted_drams[0][2], '.sc7_se_ctx', 'DATA')
            add_segment(sorted_drams[1][0], sorted_drams[1][2], '.sc7_sm_ctz', 'DATA')
        else:
            print dram_mappings
            raise ValueError('Unknown DRAM mapping set')
    else:
        print dram_mappings
        raise ValueError('Unknown DRAM mapping set')

    # Process TZRAM segments
    tzram_groups = []
    for (vaddr, paddr, size, attr) in sorted(tzram_mappings, key=lambda m:m[0]):
        inserted = False
        for i in xrange(len(tzram_groups)):
            if vaddr == tzram_groups[i][-1][0] + tzram_groups[i][-1][2] and tzram_groups[i][-1][2] != 0x40000:
                tzram_groups[i].append((vaddr, paddr, size, attr))
                inserted = True
                break
        if not inserted:
            tzram_groups.append([(vaddr, paddr, size, attr)])

    for group in tzram_groups:
        print 'Group'
        for m in group:
            print '    %x %x %x %x' % m

    # Process groups
    for group in tzram_groups:
        if len(group) > 1:
            if is_executable(group[0]):
                # .text/.rodata/.rwdata :)
                if len(group) == 2:
                    add_segment(group[0][0], group[0][2], '.text_rodata', 'CODE')
                    add_segment(group[1][0], group[1][2], '.rwdata',      'DATA')
                    load_mapping(emu, group[0])
                    load_mapping(emu, group[1])
                else:
                    assert len(group) == 3
                    add_segment(group[0][0], group[0][2], '.text',   'CODE')
                    add_segment(group[1][0], group[1][2], '.rodata', 'CONST')
                    add_segment(group[2][0], group[2][2], '.rwdata', 'DATA')
                    load_mapping(emu, group[0])
                    load_mapping(emu, group[1])
                    load_mapping(emu, group[2])
        elif is_executable(group[0]):
            assert len(group) == 1
            vaddr, paddr, size, attr = group[0]
            if size > 0x8000:
                assert len(filter(lambda g: is_executable(g[0]) and g[0][2] > 0x8000, tzram_groups)) == 1
                assert is_writable(group[0])
                add_segment(vaddr, size, '.code', 'RWX')
                load_mapping(emu, group[0])
            elif size == 0x2000:
                assert len(filter(lambda g: is_executable(g[0]) and g[0][2] == 0x2000, tzram_groups)) == 1
                add_segment(vaddr, size, '.pk2ldr', 'RWX')
                load_mapping(emu, group[0])
            else:
                assert size == 0x1000
                assert len(filter(lambda g: is_executable(g[0]) and g[0][2] == 0x1000, tzram_groups)) == 1
                add_segment(vaddr, size, '.vectors', 'CODE')
                load_mapping(emu, group[0])
        elif len(group) == 1 and (group[0][2] == 0x10000 or group[0][2] == 0x40000):
            assert len(filter(lambda g: len(g) == 1 and not is_executable(g[0]) and (g[0][2] == 0x10000 or g[0][2] == 0x40000), tzram_groups)) == 1
            assert not is_writable(group[0])
            vaddr, paddr, size, attr = group[0]
            add_segment(vaddr, size, '.tzram_ro_view', 'CONST')
        elif len(group) == 1 and group[0][2] == 0x1000:
            vaddr, paddr, size, attr = group[0]
            pk2ldr_group = filter(lambda g: is_executable(g[0]) and g[0][2] == 0x2000, tzram_groups)
            assert len(pk2ldr_group) == 1
            pk2ldr_group = pk2ldr_group[0][0]
            if paddr == emu.l3_table:
                add_segment(vaddr, size, '.l3_table', 'DATA')
            elif paddr == (emu.l3_table - 0x1000):
                add_segment(vaddr, size, '.l2_table', 'DATA')
            elif paddr == pk2ldr_group[1]:
                add_segment(vaddr, size, '.reused_stack0', 'DATA')
            elif paddr == (pk2ldr_group[1] + 0x1000):
                add_segment(vaddr, size, '.reused_stack1', 'DATA')
            elif vaddr == emu.phys_to_virt[emu.ttbr & ~0xFFF][0] or vaddr == emu.core0_stack_page:
                add_segment(vaddr, size, '.shared_data', 'DATA')
            else:
                print 'Unknown Group'
                for m in group:
                    print '    %x %x %x %x' % m
                assert False
        else:
            print 'Unknown Group'
            for m in group:
                print '    %x %x %x %x' % m
            assert False

    # Set vector types as code.
    for i, ctx in enumerate(['sp0', 'spx', 'a64', 'a32']):
        for j, kind in enumerate(['synch', 'irq', 'fiq', 'serror']):
            addr = emu.vbar + 0x200 * i + 0x80 * j
            name = '%s_%s_exception' % (ctx, kind)
            idc.create_insn(addr)
            idc.set_name(addr, name)

    # Set coldboot crt0
    idc.create_insn(emu.entrypoint)
    idc.set_name(emu.entrypoint, 'coldboot_crt0')

    # Add SMC list entries
    assert len(emu.smc_lists) == 2
    idc.set_name(emu.smc_lists_addr, 'g_smc_lists')
    for i, name in enumerate(['user', 'priv']):
        addr, num_entries, pad = emu.smc_lists[i]
        idc.set_name(addr, 'g_smc_list_%s' % name)
        for n in xrange(num_entries):
            id, access, func = up('<IIQ', emu.read_mem(addr + 0x10 * n, 0x10))
            if func == 0:
                continue
            smc_name = get_smc_name(name == 'user', id)
            process_smc(func, smc_name)

    # We're done
    return 1