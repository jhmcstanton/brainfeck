# brainfeck

A somewhat-well typed, probably pretty over engineered
brainfuck interpreter written in [Idris](https://www.idris-lang.org).

## Building

brainfeck is built using idris 1.3.2. Installation instructions
can be found [here](https://www.idris-lang.org/download/).

This project is split into 2 sub projects:

- `brainfeck-lib`
  which houses the brainfeck lexer, parser, and interpreter
- `brainfeck-cli`
  which just wraps the lib up and handles reading the provided file
  
### Steps to build:

- Install `brainfeck-lib` : `idris --install brainfeck-lib.ipkg`
  Note that this installs the package globally.
- Build `brainfeck-cli` : `idris --build brainfeck-cli.ipkg`

## Usage

`brainfeck PATH/TO/BRAINFUCK/PROGRAM`


