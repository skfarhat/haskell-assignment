#!/bin/bash

alias s='source source.sh'
alias c='ghci coinproblem.lhs test.hs'
alias o='open report.pdf'
alias l='~/Library/Haskell/bin/hlint coinproblem.lhs'
alias r='pandoc -f markdown+lhs coinproblem.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in --pdf-engine=xelatex -o report.pdf; o'