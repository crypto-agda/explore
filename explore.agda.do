exec 2>&1
echo "module explore where" >$3
git ls-files lib |
  grep -v 'Experimental\|Old\|TODO\|BigDistr\|Explore/Explorable/Fun' |
  grep '\.agda$' |
  sed -e 's|lib/\(.*\)\.agda|import \1|' |
  tr / . >>$3
