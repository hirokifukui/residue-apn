#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | awk 'NR==2{sub(/ 64x/," 63x")} {print}'
