# ida-xtensa2
This is a processor plugin for disassemblers which use IDAPython API, to support the Xtensa
core found in Espressif ESP8266. It does not support other configurations of the Xtensa
architecture, but that is probably (hopefully) easy to implement.
Originally developed for IDA (https://github.com/themadinventor/ida-xtensa),
this fork is used almost exclusively with ScratchABit open-source
disassembler: https://github.com/pfalcon/ScratchABit .

## Usage
Copy the file to the `plugins/cpu/` directory in your ScratchABit install.

Or:

Copy the file to the `procs/` directory in your IDA install.

## License
GPLv2
