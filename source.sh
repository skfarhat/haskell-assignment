#!/bin/bash

alias c='ghci coinproblem.lhs test.hs'
alias o='open report.pdf'
alias r='pandoc -f markdown+lhs coinproblem.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in --pdf-engine=xelatex -o report.pdf; o'