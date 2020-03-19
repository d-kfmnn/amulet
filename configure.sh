#!/bin/sh
die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}
usage () {
cat <<EOF
usage: configure.sh [ <option> ... ]

where <option> is one of the following

  -h      print this command line option summary
  -g      compile with debugging support
  -c      compile with assertion checking (default with '-g')

and for debugging and testing you can also use

  --test-only          do not compile checker but only unit test
  --verbose-parsing    print scanned tokens and parsed polynomials
EOF
}
debug=no
check=undefined
testonly=no
verboseparsing=no
test
while [ $# -gt 0 ]
do
  case "$1" in
    -h|--help) usage; exit 0;;
    -c) check=yes;;
    -g) debug=yes;;
    --test-only) testonly=yes;;
    --verbose-parsing) verboseparsing=yes;;
    -*) die "invalid option '$1' (try '-h')";;
  esac
  shift
done
if [ $debug = yes ]
then
  check=yes
elif [ $check = undefined ]
then
  check=no
fi
CFLAGS="-Wall -Wextra"
if [ $debug = yes ]
then
  CFLAGS="$CFLAGS -g3"
else
  CFLAGS="$CFLAGS -O3"
fi
[ $check = no ] && CFLAGS="$CFLAGS -DNDEBUG"
[ $testonly = yes ] && CFLAGS="$CFLAGS -DTESTONLY"
[ $verboseparsing = yes ] && CFLAGS="$CFLAGS -DVERBOSEPARSING"
[ "$CC" = "" ] && CC=gcc


if [ -d /tmp/ ]
then
  tmp=/tmp/pacman-configure-$$
  trap "rm -f $tmp*" 2
cat >$tmp.c <<EOF
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>
int main () {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  double t = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  t += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  size_t s = ((size_t) u.ru_maxrss) << 10;
  printf ("%f seconds\n%zu bytes\n", t, s);
  return 42;
}
EOF
  if $CC $CFLAGS $tmp.c -o $tmp.exe 1>/dev/null 2>/dev/null
  then
    $tmp.exe 1>/dev/null 2>/dev/null
    [ $? = 42 ] && CFLAGS="$CFLAGS -DHAVEGETRUSAGE"
  fi
  rm -f $tmp*
cat >$tmp.c <<EOF
#include <stdio.h>
int main () {
  FILE * file = fopen ("configure.sh", "r");
  if (!file) return 1;
  int ch = getc_unlocked (file);
  fclose (file);
  return ch == '#' ? 42 : 1;
}
EOF
  if $CC $CFLAGS $tmp.c -o $tmp.exe 1>/dev/null 2>/dev/null
  then
    $tmp.exe 1>/dev/null 2>/dev/null
    [ $? = 42 ] && CFLAGS="$CFLAGS -DHAVEUNLOCKEDIO"
  fi
  rm -f $tmp*
fi
AIGLIB="aiger/aiger.o"


echo "$CC $CFLAGS $AIGLIB"
rm -f makefile
sed \
  -e "s,@CC@,$CC," \
  -e "s,@CFLAGS@,$CFLAGS," \
  -e "s,@AIGLIB@,$AIGLIB," \
makefile.in > makefile
