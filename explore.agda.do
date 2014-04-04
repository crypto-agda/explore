#!/bin/bash -ue
echo "module explore where" >$1
git ls-files lib |
  grep -v 'Experimental\|Old\|TODO\|BigDistr\|Explore/Explorable/Fun' |
  grep '\.agda$' |
  sed -e 's|lib/\(.*\)\.agda|import \1|' |
  tr / . >>$1
