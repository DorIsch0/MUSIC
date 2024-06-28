# MUSIC
MIDI-Using System of Interacting with Computers

## Introduction
This is a compiler for a self-designed programming language named MUSIC, the MIDI-Using System of Interacting with Computers. MUSIC uses MIDI-files as source code. It has the following design goals:
1. MUSIC shall be Turing complete, i.e. it should be able to do everything any other programming language can do.
2. It shall be possible to write programms that sound good while not being to long.
3. For musical interpretation as well as for interpretation by a computer only audible data shall be used, e.g. file meta-data should not have an influence on the output of the program.
MUSIC objectively reaches goal 1 and 3 and works towards the second goal by allowing multiple musical inputs to correspond to the same programm. You can read about how this is accomplished in the documentation section under "Translating from MIDI to Intermediate language".
The compiler uses LLVM.

## Installation and Usage
I do not promise this to work on any machine but my own (Linux Ubuntu 22.04.4, 64-bit).
You need clang.
Clone the repository into a directory. `cd` into that directory. Then run
``src/compile.sh``
**(only run from that directory!)** to get the compiler `bin/music`. You can then run
``bin/music <SOURCE> [-d<n>] [-o<OUTPUT>] [-i]``
**(again, only from that directory!)** with the following arguments:
`SOURCE`: The MIDI-file (or intermediate language file for `-i`).
`-d<n>`: Set the debug level to n. Default is 0 with no debug output.
- on level 1, every argument you got along the translation from midi to intermediate code (inter) is printed, plus the resulting inter code at the end of the translation stage
- on level 2, the same as on level 1 gets printed plus the list of notes at the start of the program, the type of each translated argument, the sum of every translated token and, in the compilation stage, every line of the inter code before it gets compiled
- on level 3, the same as on level 2 gets printed plus the list of notes every time a token gets translated
`-o<OUTPUT>`: save the resulting .ll-file under OUTPUT (default is `out/out.ll`)
`-i`: indicates that the input file already is an intermediate code file
Finally, you can run `clang` on your output file and then execute it.
