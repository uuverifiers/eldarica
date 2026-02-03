#!/bin/sh

if [ $(uname) = "Linux" -o $(uname) = "Darwin" ]; then
    pathCmd="readlink -f"
else
    pathCmd="realpath"
fi

BASEDIR=`dirname "$($pathCmd $0)"`
NATIVE=$BASEDIR/target/native-image/Eldarica

if [ -f $NATIVE ]; then
    exec $NATIVE "$@"
else
    ."$BASEDIR/eldEnv"
    exec $LAZABS_CMD lazabs.Main "$@"
fi
