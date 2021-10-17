

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


JLEX_PATH:=/usr/share/java/JLex.jar
CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR)/lib/java-cup-11a.jar:$(PARSER_BASEDIR):$(JLEX_PATH)

JAVAC:=javac
#JAVAC_FLAGS:=-target 1.5

JAVA:=java
JAVA_FLAGS:=


export CLASSPATH


all: cc-parser.jar lazabs/horn/concurrency/concurrentC/Test.class


cc-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Absyn/concurrentC.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/sym.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Yylex.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/cc-parser.jar lazabs


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf lazabs
	rm -rf concurrentC.tex concurrentC.dvi concurrentC.aux concurrentC.log concurrentC.ps


# just any of the files that is created by bnfc
concurrentC.tex: concurrentC.cf
	bnfc -p lazabs.horn.concurrency -java1.5 concurrentC.cf

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Absyn/concurrentC.java: concurrentC.cf
	bnfc -p lazabs.horn.concurrency -java1.5 concurrentC.cf

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Absyn/concurrentC.class: $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Absyn/concurrentC.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/concurrency/concurrentC/Absyn/*.java

lazabs/horn/concurrency/concurrentC/Yylex.java: lazabs/horn/concurrency/concurrentC/Yylex
#       remove some quotes that JLex does not accept
#	sed 's/\\\^/\^/g' <smtlib/Yylex >smtlib/Yylex.temp
#	mv smtlib/Yylex.temp smtlib/Yylex
#       quote dashes "-"
#	sed 's/\\\+-/\\+\\-/g' <smtlib/Yylex >smtlib/Yylex.temp
#	mv smtlib/Yylex.temp smtlib/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} lazabs/horn/concurrency/concurrentC/Yylex

lazabs/horn/concurrency/concurrentC/sym.java lazabs/horn/concurrency/concurrentC/parser.java: lazabs/horn/concurrency/concurrentC/concurrentC.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} lazabs/horn/concurrency/concurrentC/concurrentC.cup
	mv sym.java parser.java lazabs/horn/concurrency/concurrentC/

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Yylex.class: lazabs/horn/concurrency/concurrentC/Yylex.java lazabs/horn/concurrency/concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/concurrency/concurrentC/Yylex.java

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/sym.class: lazabs/horn/concurrency/concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/concurrency/concurrentC/sym.java

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/parser.class: lazabs/horn/concurrency/concurrentC/parser.java lazabs/horn/concurrency/concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/concurrency/concurrentC/parser.java

lazabs/horn/concurrency/concurrentC/PrettyPrinterNonStatic.java: lazabs/horn/concurrency/concurrentC/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <lazabs/horn/concurrency/concurrentC/PrettyPrinter.java | sed 's/static//g' >lazabs/horn/concurrency/concurrentC/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/PrettyPrinter.class: lazabs/horn/concurrency/concurrentC/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/concurrency/concurrentC/PrettyPrinter.java

$(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/PrettyPrinterNonStatic.class: lazabs/horn/concurrency/concurrentC/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/concurrency/concurrentC/PrettyPrinterNonStatic.java

lazabs/horn/concurrency/concurrentC/Test.class: lazabs/horn/concurrency/concurrentC/Test.java $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/PrettyPrinter.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/Yylex.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/parser.class $(PARSER_BINDIR)/lazabs/horn/concurrency/concurrentC/sym.class
	${JAVAC} ${JAVAC_FLAGS} lazabs/horn/concurrency/concurrentC/Test.java

concurrentC.dvi: concurrentC.tex
	${LATEX} concurrentC.tex

concurrentC.pdf: concurrentC.dvi
	${DVIPDF} concurrentC.dvi

concurrentC.ps: concurrentC.dvi
	${DVIPS} concurrentC.dvi -o concurrentC.ps
