#!/bin/sh
# Copyright 1998 Lars T Hansen.
#
# $Id: twobit,v 1.3 1998/12/18 22:31:07 lth Exp $
#
# Shell script to run twobit.
#
# Usage: twobit [larceny-options ...] [program-options ...]
# where larceny-options are valid options for larceny, and program-
# options are anything else.  If you want to pass an option
# that is a valid larceny-option as a program-option, then use -args
# to separate program options and larceny options.
#
# For example,
#  larceny -np -foo         ; -np is a larc.opt., -foo a prog.opt.
#  larceny -np -args -load  ; -np is a larc.opt., -args -load a prog.opt.

# EDIT THIS PATH TO SUIT YOUR SYSTEM.
LARCENY_PATH=/scratch/samth/larceny
unset LARGS
unset PARGS
SMALL=0
while [ "$1" != "" ]; do 
  case $1 in
    -annoy-user | -annoy-user-greatly | -gen | -help | -nobreak | -nostatic | \
    -np | -quiet | -reorganize-and-dump | -stats | -step | -stopcopy)
      LARGS="$LARGS $1"; shift 
      ;;
    -areas | -load | -max | -rhash | -size* | -ssb | -steps | -stepsize | \
    -ticks)
      LARGS="$LARGS $1 $2"; shift; shift 
      ;;
    -args) PARGS="$@"; break ;;
    *) PARGS="-args $@"; break ;;
  esac
done
exec $LARCENY_PATH/larceny.bin $LARGS $LARCENY_PATH/twobit.heap $PARGS
