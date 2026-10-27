#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | sed '1s/.*/perm_dups 1/'
