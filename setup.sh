#!/bin/bash

holdir=$HOLDIR
workDir=$(pwd)

echo "Starting setup for Lassie."

#cd $workDir/sempre
#./pull-dependencies core interactive
#
#ant core interactive

cd $workDir/src

$holdir/bin/Holmake

echo "Setup completed."
echo "Start Sempre by running \`cd sempre\` then \`interactive/run @mode=lassie\`"
echo "Or \`open Lassie\` in an HOL4 session after setting LASSIEDIR to $(pwd)"
