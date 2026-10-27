#!/bin/sh
# negative-control fake checkers; each prints something wrong
cd "$(dirname "$0")"
cat > exit7.sh <<'X'
#!/bin/sh
exit 7
X
cat > empty.sh <<'X'
#!/bin/sh
exit 0
X
cat > header_only.sh <<'X'
#!/bin/sh
echo "perm_dups 0"
X
cat > nonperm.sh <<'X'
#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | sed '1s/.*/perm_dups 1/'
X
cat > dupdir.sh <<'X'
#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | awk 'NR==2{print; print; next} NR==3{next} {print}'
X
cat > badclass.sh <<'X'
#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | awk 'NR==2{sub(/^exc/,"ord")} {print}'
X
cat > badmass.sh <<'X'
#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | awk 'NR==2{sub(/ 64x/," 63x")} {print}'
X
cat > partial.sh <<'X'
#!/bin/sh
"$(dirname "$0")/../grddt3" "$@" | head -n 100
X
chmod +x *.sh
