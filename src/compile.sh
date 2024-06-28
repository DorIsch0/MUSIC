mkdir -p out
mkdir -p bin
clang -S -emit-llvm -o src/input.ll src/input.c && echo '#include <string>'$'\n'$"const string INPUTLLSTR=R\"?($(cat src/input.ll))?\";" > include/inputLLHeaderFile.h && clang++ -o bin/music src/main.cpp src/midi2code.cpp src/midifile/src/MidiFile.cpp src/midifile/src/MidiEvent.cpp src/midifile/src/MidiEventList.cpp src/midifile/src/Binasc.cpp src/midifile/src/MidiMessage.cpp -Iinclude -Isrc/midifile/include -L/usr/lib/x86_64-linux-gnu -lphobos2 -pthread `llvm-config --cxxflags --ldflags --system-libs --libs core`
