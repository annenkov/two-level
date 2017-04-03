#!/bin/bash -e

function cleanup() {
    [ -z "$tmp" ] || rm -fr "$tmp"
}

function refname() {
    sed -n "/\\\\newlabel{$1@cref}/ s/\\\\newlabel{[^}]*}{{\[\([^]]*\)\]\[\([0-9]*\)\].*/\1 \2/g p" "$tmp/two-level.aux"
}

mapfile -t refs < <(grep -Ih -- '-- ref:' *.lean | sed 's/.*-- ref://g')

echo "${#refs[@]} references"

trap cleanup EXIT
tmp=`mktemp -d`
cp ../paper/{two-level.tex,header.tex} "$tmp"

( cd "$tmp"
  sed -i '/^\\title{/ i \\n\\usepackage{cleveref}' two-level.tex
  pdflatex two-level.tex 2>&1 >/dev/null )

for ref in "${refs[@]}"; do
    name="$(refname "$ref")"
    echo "$ref ==> $name"
    sed -i -- 's/-- ref:'"$ref"'/-- '"$name"'/g' *.lean
done
