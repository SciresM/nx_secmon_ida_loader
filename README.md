# nx_secmon_ida_loader

![License](https://img.shields.io/badge/license-ISC-blue.svg)

This is a script to automate loading a Secure Monitor binary for the Nintendo Switch into IDA PRO.

It automatically performs binary loading by emulating the secure monitor to determine what memory mappings it sets up.

Additionally, using the same emulation techniques it automatically labels entrypoint, exception vectors, and SMC tables (+ all entries in the tables).

To use, decrypt the `package1` firmware package, and load.

Note: use of this script requires unicorn to be installed.
