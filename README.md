# curry-addtypes - A tool to add missing type signatures in a Curry program

This package contains the tool `curry-addtypes` which adds
missing type signatures to top-level operations in a Curry module.
Moreover, it contains a library to process strings containing
Curry source code and classifies it into a few standard categories

## Installing the tool

The tool can be directly installed by the command

    > cypm install addtypes

This installs the executable `curry-addtypes` in the bin directory of CPM.


## Using the tool

If the bin directory of CPM (default: `~/.cpm/bin`) is in your path,
execute the tool with the Curry program where type signatures should
be added, e.g.,

    > curry-addtypes LazyProgram

This command replaces the program `LazyProgram.curry` by a new
program text where type signatures to top-level operations
have been added. The old version of the program is saved
to `LazyProgram_ORG.curry`.
