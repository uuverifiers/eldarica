#!/bin/sh

if [ $(uname) = "Linux" -o $(uname) = "Darwin" ]; then
    pathCmd="readlink -f"
else
    pathCmd="realpath"
fi

BASEDIR=`dirname "$($pathCmd $0)"`

. "$BASEDIR/eldEnv"

exec $LAZABS_CMD lazabs.Main "$@"
