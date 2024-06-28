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
Also I do not guarantee that this works at all. My tests were succesful, but few.  
You need clang.  
Clone the repository into a directory. `cd` into that directory. Then run  
``src/compile.sh``  
**(only run from that directory!)** to get the compiler `bin/music`. You can then run  
``bin/music <SOURCE> [-d<n>] [-o<OUTPUT>] [-i]``  
**(again, only from that directory!)** with the following arguments:  
- `SOURCE`: The MIDI-file (or intermediate language file for `-i`).  
- `-d<n>`: Set the debug level to n. Default is 0 with no debug output. 
  - on level 1, every argument you got along the translation from midi to intermediate code (inter) is printed, plus the resulting inter code at the end of the translation stage
  - on level 2, the same as on level 1 gets printed plus the list of notes at the start of the program, the type of each translated argument, the sum of every translated token and, in the compilation stage, every line of the inter code before it gets compiled
  - on level 3, the same as on level 2 gets printed plus the list of notes every time a token gets translated
- `-o<OUTPUT>`: save the resulting .ll-file under OUTPUT (default is `out/out.ll`)  
- `-i`: indicates that the input file already is an intermediate code file  

Finally, you can run `clang` on your output file and then execute it.  

## Examples
There is a directory of examples. Take a look at them - it makes understanding the documentation way easier. The intermediate language examples are found in `examples/inter`, the midi examples in `examples/midi`. The `examples/mscz` directory holds a MuseScore 3 project of the dart.mid example. Here is a list of all examples and what they do:
- HelloWorld.inter and HelloWorld.mid: What did you expect?
- dart.inter and dart.mid: computes Tau using the dartboard method
- turing.inter and turing.mid: a working turing machine without proper documentation.
Of those examples, only dart.mid follows the second design goal of sounding good, the other two were automatically created using `tools/inter2notes.py`.

## Documentation
The compilation follows two steps: First, the MIDI data is translated into an intermediate language, which is then compiled into the .ll file. I will first introduce the intermediate language and then explain the translation stage.

### The intermediate language
#### Overview
The intermediate language is pretty close to an assembly language. Each line consists of an operand followed by a number of arguments. The arguments can be one of five kinds: variable (v), literal (l), something (s), type (t) or label (l). As an example (which sadly uses information found below - just keep reading if you don't understand it yet), the `add` operand takes three arguments, the first two of type s, the third of type v, so for example adding the variables `v1` and `v2` and saving the result in `v3` would be written as `add v1 v2 v3`.

#### The kinds of arguments
There are six groups of types: Integers, floating point, pointers, arrays, dynamic arrays and collections (which have a bad name - they really are structs).
- Integers are denoted as `i<bitwidth>` where bidwitdth is 8, 16, 32 or 64, e.g. `i8` for a C char or `i16` for a C short
- Floating points are denoted as `f32` for a float and `f64` for a double
- Pointers are denoted as `ptr(<subtype>)` where subtype is the type of the value the pointer points to, e.g. `ptr(i8)` for what C calls a `char*`
- Arrays are denoted as `arr!<length>(<subtype>)` where length is the (fixed) length of the array and subtype is the type of values the array holds, e.g. `arr!5(i8)` for what C calls a `char <variable name>[5]`
- Dynamic arrays are denoted as `darr(<subtype>)` where subtype is the type of values the dynamic array holds, for example `darr(i8)` for something similar to C++ string
- Collections are denoted as `coll{<subtype0>,<subtype1>,...,}` (don't forget the comma at the end) where subtypeN is denoting the type of the value stored at the N's place in the collection, e.g. `coll{f32,f32,f32,}` for storing a point in space

Variables and literals are strongly typed. You do not have to declare variables though, they are automatically created on first use and inherit the type assigned to them.  
Variable names have to start with a `v` and will work if they follow standard variable naming conventions of e.g. C. For example, `v0` or `vreturnValue` would be valid variable names.  

Literals are written in the form `l<type>[<value>]`, where type follows the same pattern as a type argument (see above) and the value is written as follows:
- for an integer or floating point typed literal as usually, e.g. `li64[-5]` for an int of value -5, or `lf64[-3.]` for a double of value -3.0
- for a ptr, arr or darr typed literal as nothing, each literal of those types is uninitiallized and using its contents yields undefinied behaviour. Examples: `lptr(i64)[]` gives a null pointer, `larr!5(i64)[]` gives an empty array of five i64's and `ldarr(i64)[]` gives an empty darr (length 0) of i64's.
- for a coll as a comma-seperated list of something-values (see below) with an additional comma at the end and no spaces in between, e.g. `lcoll{f32,f32,f32,}[lf32[3.],lf32[-1.1],v3,]` for a variable named `v3` of type `f32`

Somethings are either variables or literals (they are used everywhere where the operand could take a literal value or a variable value) and are written the same way, e.g. when a something is expected, `v3` would be the value of the variable `v3` while `li32[4]` would instead be an integer value of type i32 and value 4.

Labels are written in the same form as variables except for an `a` instead of a `v`, e.g. `aloopStart`. They are used as points the code execution can jump to, so they are crucial for control flow.

#### The operands
All operands are listed along with their required argument kinds in `src/opsNew.csv`.

##### nop
Does nothing and takes no argument. Usage discouraged.

##### str s v
Stores the value of s into v. darrs, arrs and colls will be copied.

##### strGlob s v
Same as str but with a global variable v accessible from any scope in any function.

##### cast v1 t v2
Cast v1 to type t and store the result into v2. Casting is supported in the following ways:
- integer to
  - integer (if I do not specify otherwise, they may always be of different bitwidth)
  - float
  - ptr
- float to
  - float
  - integer
- ptr to
  - ptr (possibly of different subtype)
  - integer
  - arr of same subtype
  - darr of same subtype
- arr to
  - arr of compatible subtype (where casting from one subtype to the other would be possible)
  - darr of same subtype
- darr to
  - darr of compatible subtype
  - arr of same subtype

##### add s1 s2 v
Adds s1 and s2 and stores the result into v. Adding is supported in the following ways:
- integer + integer and float + float
- integer + ptr and ptr + integer (shifting the ptr for the desired amount)
- darr + darr and arr + arr, in both cases of same subtype (concatenating the two)

##### sub s1 s2 v
Subtracts s2 from s1 and stores the result into v. Subtracting is supported in the following ways:
- integer - integer and float - float
- ptr - integer (shifting the ptr for the desired amount)

##### mul s1 s2 v
Multiplies s1 and s2 and stores the result into v. Multiplying is supported in the following ways:
- integer * integer and float * float (possibly different bitwidths)
- darr * integer and integer * darr (concatenating the darr to itself integer amounts)

##### div s1 s2 v
Subtracts s2 from s1 and stores the result into v. Subtracting is supported in the following ways:
- integer / integer and float / float

##### eq s1 s2 v
Compares s1 and s2 and stores true (1) if they are equal and false (0) else. The resulting variable has the normally non accessible type i1. The comparison works as follows:
- integer == integer, float == float: Do they have the same value?
- ptr == ptr: Do they point to the same address?
- arr == arr and darr == darr (in both cases of same subtype): Are they the same length and all elements equal?

##### gt s1 s2 v
Compares s1 and s2 and stores true if s1 is greater than s2 and false else. The comparison works as follows:
- integer > integer, float > float, ptr > ptr as expected

##### gte s1 s2 v
Same as gt, but also stores true if s1 and s2 are equal. It is equivalent to gt s2 s1 v and then not-ing the result.

##### not s v
Stores a result in v. If s is of type arr, darr or coll, that result will always be false. If s is of type integer, float or pointer, it will be true if and only if the value of s is 0 (or, equivalently, false).

##### bnot s v
Flips all bits of s (which must be of type integer) and stores the result in v.

##### is s v
Same as not, but with the exact opposite result.

##### and s1 s2 v
s1 and s2 must be integers of the same bitwidth. The result of the bitwise and of s1 and s2 will be stored into v. If s1 and s2 are i1's, that is the same as the logical and.

##### or s1 s2 v
Same as and, but with the bitwise or instead.

##### splice s1 s2 s3 v
s1 has to be of type arr or darr, s2 and s3 have to be integers between 0 and the length of s1 with s3>s2. The result is a new darr consisting of all elements of s1 between s2 inclusively and s3 exclusively.

##### append v s
v has to be a darr and s has to be of the subtype of v. The length of v will be increased by one and s will be stored at its last index.

##### insert v s1 s2
v has to be a darr, s1 has to be of the subtype of v and s2 has to be an integer between 0 and the length of v. The length of v will be increased by one, everything from index s2 up to the end will be shifted by one index to the right and s will be stored at index s2.

##### pop v1 s v2
v1 has to be a darr and s has to be an integer between 0 and the length of v1. The element at index s of v1 will be removed, everything after it shifted left by one index and the length of v1 will be decreased by one. The removed element will be stored into v2.

##### popLast v1 v2
Same as pop with s being the last index of v1.

##### getAt v1 s v2
There are two ways in which this can work:
- v1 has to be a darr, arr or coll and s has to be an integer between 0 and the length of v1. The element at index s of v1 will be stored into v2.
- v1 has to be a ptr and s has to be zero. The pointee of v1 gets stored into v2.

##### setAt v s1 s2
There are two ways in which this can work:
- v has to be a darr, arr or coll, s1 has to be an integer between 0 and the length of v1 and s2 has to be of the subtype of v. s2 is stored at index s1 of v.
- v has to be a darr, arr or coll, s1 has to be zero and s2 has to be of the subtype of v. s2 is stored at the address v is pointing to.

##### getPtr v1 v2
Get a pointer pointing to v1 and store it into v2.

##### jmpif s a
s has to be an integer, float or ptr. If the value in s is not 0 (or, equivalently, if s is true), code execution will continue after the label a, else it will continue here. Jumping out of the current function, into a function, out of the current scope, into a scope or to a function name yields undefined behavior.

##### jmp a
Code execution will continue at label a. Jumping out of the current function, into a function, out of the current scope, into a scope or to a function name yields undefined behavior.

##### def a t v
Start a function definition. Everything from here to the ret operand will be inside the function. a is the name of the function, t is the type of the function argument (has to be a coll type) and v is the name of the argument variable. In MUSIC, each function has exactly one argument, which is a coll. For functions without arguments, use an empty coll. For functions with a return value, use a coll holding a ptr to the return value's variable.

##### call a s
Call function a with argument s. Code execution will continue after the def statement for a and return here when ret is reached.  
Calling a label that is not a function yields undefined behavior.

##### ret
Return from a function. There may be only one ret per function.

##### lbl a
Mark this point of the code as the label a. You may jmp or jmpif here.

##### inp t v
Wait for an input into stdin, interpret the result as a value of type t and store it into v. You can only input integers and floats.

##### inpS v
Wait for an input into stdin, convert each character to an i8 and store them as a darr(i8) into v.

##### prt s
Print s to the screen. Integers and floats are printed as expected, ptrs print their pointees address in hexadecimal form. For arrs and darrs there will be a opening bracket followed by the elements of the arr (each one followed by a comma) followed by a closing bracket. The same goes for colls, except with curly brackets.

##### len s v
s has to be a arr, coll or darr. The number of elements in s will be stored into v.

##### destroy v
v will be deleted from the variable list. If v is a darr, the used memory will be freed.

##### startScope
Starts a scope. Don't know what you expected.

##### endScope
I forgot...

##### prtS s
s has to be a darr(i8). Interpret each i8 as a character and print them to the screen.

##### exit
Terminate the program.


### Translating from MIDI to Intermediate language
The basic concept of representing the intermediate language in MIDI works by representing each token as a sequence of notes where the first and the last chord share the same lowest note and no chord in between does so. The pitches of the notes in between, more accurately: The signed distance from middle C (everything above has positive sign, everthing below negative) are used to represent the value of the token. We will call those signed distances of notes between the enclosing chords shifted pitch values or shortly SPVs. It works as follows:

#### Encoding an operand
The SPVs are summed up. The sum modulo 41 is the index of the operand in src/opsNew.csv. (There are 39 operands plus two nops in case I decide to expand the language later.)

#### Encoding a type
The SPVs are summed up. The sum modulo 29 is the index of the type in tools/types.txt. If the type is an integer or float, we are done. If the type is a ptr or darr, the next token (let's call it NT) will be its subtype.  
If it is an arr, NT will represent its length: If the enclosing chords of NT have the same average velocity, the length will be the sum of the SPVs of NT, else it will be the number of chords in NT, i.e. the number of MIDI ticks between the enclosing chords of NT on which a note is started. The token after NT will then represent the subtype.  
If the type is a coll, NT will represent its subtypes. All notes between the enclosing chords of NT are treated as a seperate list of tokens, i.e. we search that list for matching lowest notes and treat that part as a token for a subtype. You go through the list adding subtype after subtype until you reach the end.

#### Encoding a variable or a label
The SPVs are summed up. We then create the variable/label named `v<sum>` or `a<sum>` respectively. For example, if the sum is 40, the variable would be called `v40`.

#### Encoding a literal
The first token encodes the type. After the type token(s), the next token (NT) encodes the value (except for ptr, arr and darr, where there is no value). If the type is
- an integer, the value of the literal is
  - the sum of the SPVs of NT if the enclosing chords of NT have the same average velocity
  - the number of chords in the NT else
- a float, the value is a part before the decimal point and a point after, where
  - the part before is encoded like an integer (see above) and
  - the part after is encoded in the following way: You go through each chord and sum up the SPVs of that chord. You take the result mod 10 and append it to the number.
- a coll, NT holds all "subvalues": You treat the list of notes between the closing chords of NT as a seperate list of tokens holding the subvalues. Each subvalue is a something.

#### Encoding a something
Same as encoding a variable or a literal, but if the enclosing chords of the first token have the same average velocity, it is a variable, else it is a literal.

## Tips for writing a MUSIC-programm
If you want to write a MUSIC-programm, I recommend the following workflow:
You may or may not want to write your program in a higher level language first, Python for example, and then translate it into the intermediate language. You could also write it directly in the intermediate language.  
The second step is optimizing your intermediate language code for length as much as possible. You want to have to write as few notes as possible in the end, because that will be the hardest part of the project - keep in mind, you will at the same time compose music and write a program, which - surprise - is not easy.  
Then open up your favorite MIDI editor (I use MuseScore) and beginn to write some music. You should be oriented towards the opening and closing of your tokens. Try not to make those tokens to short to leave a bit of space for correction.
When you made one length of a token, you compile the MIDI file on debug level 2 and look how far you are off from your desired token value. You then correct your MIDI file such that the value is correct. Now just repeat that for your whole code and you are done.
Also, keep a list of your used variables and labels.
