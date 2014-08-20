#!/bin/sh

if [ $(uname) = "Linux" ]; then
    pathCmd="readlink -f"
elif [ $(uname) = "Darwin" ]; then
    pathCmd="stat -f %N"
else
    pathCmd="realpath"
fi

BASEDIR=`dirname $($pathCmd $0)`

. $BASEDIR/eldEnv

exec $LAZABS_CMD lazabs.Main "$@"
