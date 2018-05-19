#!/usr/bin/env scala

import scala.io.Source

val filename = args(0)
for (line <- Source.fromFile(filename).getLines) {
    println(line.replaceAll("Int","(_ BitVec 32)").replaceAll("\\(\\*","(bvmul").replaceAll("(?<!BitVec( | 3))[0-9]+","(_ bv$0 32)"))
}