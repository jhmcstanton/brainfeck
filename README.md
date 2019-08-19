# brainfeck

A somewhat-well typed, probably pretty over engineered
brainfuck interpreter written in [Idris](https://www.idris-lang.org).

## Building

brainfeck is built using idris 1.3.2. Installation instructions
can be found [here](https://www.idris-lang.org/download/).

This project is split into 3 sub projects:

- `brainfeck-lib`
  which houses the brainfeck lexer, parser, and interpreter
- `brainfeck-cli`
  which just wraps the lib up and handles reading a provided file
  using the C backend
- `brainfeck-web`
  which calls the library from JS using the javascript backend. This
  is reliant on the [index.html](./index.html) found in this repo.
  
### Steps to build:

- Install `brainfeck-lib` : `idris --install brainfeck-lib.ipkg`
  Note that this installs the package globally.
- Build `brainfeck-cli` : `idris --build brainfeck-cli.ipkg`
- Build `brainfeck-web` : `idris --build brainfeck-web.ipkg`

## Usage

### CLI 

`brainfeck PATH/TO/BRAINFUCK/PROGRAM`

### Web

Or head over to [the gh-pages hosted brainfeck-web implementation](https://jhmcstanton.com/brainfeck).
This version is using the js backend for idris. The compiled code can be found
in [brainfeck.js](./brainfeck.js).

## TODO

Add example links / imports to index.html.
