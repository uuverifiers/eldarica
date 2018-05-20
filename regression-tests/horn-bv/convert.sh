#!/usr/bin/env scala

import scala.io.Source

val filename = args(0)
for (line <- Source.fromFile(filename).getLines) {
	if (line.replaceAll("\\s","").startsWith(";"))
		println(line)
	else
		println(line.replaceAll("Int","(_ BitVec 32)")
		.replaceAll("\\*","bvmul")
		.replaceAll("\\+","bvadd")
		.replaceAll("(?<![a-zA-Z])-","bvsub")
		.replaceAll("<=","bvsle")
		.replaceAll(">=","bvsge")
		.replaceAll("<","bvslt")
		.replaceAll("(?<!=)>","bvsgt")
		.replaceAll("(?<!(BitVec( | 3))|[a-zA-Z])[0-9]+","(_ bv$0 32)")
		)
}