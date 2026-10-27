#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | head -n 100
