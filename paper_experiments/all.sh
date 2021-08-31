#!/bin/sh

RunSynbit() {
    timeout $timeoutSec stack exec synbit $1
    if [ $? != 0 ]; then
      echo "timeout ($timeoutSec s)"
    fi
}

timeoutSec=30
if [ $# != 0 ]; then
  timeoutSec=$1
fi

for file in `\find . -name 'spec.hobit'`; do
    RunSynbit $file
    echo ""
    echo ""
done
