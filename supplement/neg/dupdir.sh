#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | awk 'NR==2{print; print; next} NR==3{next} {print}'
