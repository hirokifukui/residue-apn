#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | awk 'NR==2{sub(/^exc/,"ord")} {print}'
