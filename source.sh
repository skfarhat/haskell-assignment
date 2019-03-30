#!/bin/bash

alias r='pandoc -f markdown+lhs questions.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in --pdf-engine=xelatex -o questions.pdf'
