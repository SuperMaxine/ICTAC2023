#!/bin/bash

# read 2 parameters from command line, the first is the type of the check, should be one of the ["CC", "EQ", "PO", "PA"]
# the second is the path of the file to be checked

# get current directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# run "ocaml [first parameter].ml [second parameter]"
ocaml $DIR/$1.ml $2