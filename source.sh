#!/bin/bash

alias s='source source.sh'
alias c='ghci coinproblem.lhs test.hs'
alias o='open report.pdf'
alias l='~/Library/Haskell/bin/hlint coinproblem.lhs'
alias r='pandoc -f markdown+lhs coinproblem.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in --pdf-engine=xelatex -o report.pdf; o'
alias r2='pandoc --verbose -f markdown+lhs coinproblem.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in --pdf-engine=xelatex --template default.latex -o report.pdf; o'
alias r3='pandoc -f markdown+lhs coinproblem.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in --pdf-engine=xelatex -o report.pdf; o'
alias r4='pandoc --verbose -f markdown+lhs --highlight-style my_style.theme coinproblem.lhs -V papersize:a4 -V fontsize:12pt -V geometry:margin=1in -V mainfont=Helvetica --pdf-engine=xelatex --template default.latex -o report.pdf; o'