

CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


JLEX_PATH:=/usr/share/java/JLex.jar
CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR)/../lib/java-cup-11a.jar:$(PARSER_BASEDIR):$(JLEX_PATH)

JAVAC:=javac
#JAVAC_FLAGS:=-target 1.5

JAVA:=java
JAVA_FLAGS:=


export CLASSPATH


all: cc-parser.jar concurrentC/Test.class


cc-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/concurrentC/Absyn/concurrentC.class $(PARSER_BINDIR)/concurrentC/sym.class $(PARSER_BINDIR)/concurrentC/Yylex.class $(PARSER_BINDIR)/concurrentC/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/concurrentC/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/cc-parser.jar concurrentC


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf concurrentC
	rm -rf concurrentC.tex concurrentC.dvi concurrentC.aux concurrentC.log concurrentC.ps


# just any of the files that is created by bnfc
concurrentC.tex: concurrentC.cf
	bnfc -java1.5 concurrentC.cf

$(PARSER_BINDIR)/concurrentC/Absyn/concurrentC.java: concurrentC.cf
	bnfc -java1.5 concurrentC.cf

$(PARSER_BINDIR)/concurrentC/Absyn/concurrentC.class: $(PARSER_BINDIR)/concurrentC/Absyn/concurrentC.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) concurrentC/Absyn/*.java

concurrentC/Yylex.java: concurrentC/Yylex
#       remove some quotes that JLex does not accept
#	sed 's/\\\^/\^/g' <smtlib/Yylex >smtlib/Yylex.temp
#	mv smtlib/Yylex.temp smtlib/Yylex
#       quote dashes "-"
#	sed 's/\\\+-/\\+\\-/g' <smtlib/Yylex >smtlib/Yylex.temp
#	mv smtlib/Yylex.temp smtlib/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} concurrentC/Yylex

concurrentC/sym.java concurrentC/parser.java: concurrentC/concurrentC.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} concurrentC/concurrentC.cup
	mv sym.java parser.java concurrentC/

$(PARSER_BINDIR)/concurrentC/Yylex.class: concurrentC/Yylex.java concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) concurrentC/Yylex.java

$(PARSER_BINDIR)/concurrentC/sym.class: concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) concurrentC/sym.java

$(PARSER_BINDIR)/concurrentC/parser.class: concurrentC/parser.java concurrentC/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) concurrentC/parser.java

concurrentC/PrettyPrinterNonStatic.java: concurrentC/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <concurrentC/PrettyPrinter.java | sed 's/static//g' >concurrentC/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/concurrentC/PrettyPrinter.class: concurrentC/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) concurrentC/PrettyPrinter.java

$(PARSER_BINDIR)/concurrentC/PrettyPrinterNonStatic.class: concurrentC/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) concurrentC/PrettyPrinterNonStatic.java

concurrentC/Test.class: concurrentC/Test.java $(PARSER_BINDIR)/concurrentC/PrettyPrinter.class $(PARSER_BINDIR)/concurrentC/Yylex.class $(PARSER_BINDIR)/concurrentC/parser.class $(PARSER_BINDIR)/concurrentC/sym.class
	${JAVAC} ${JAVAC_FLAGS} concurrentC/Test.java

concurrentC.dvi: concurrentC.tex
	${LATEX} concurrentC.tex

concurrentC.pdf: concurrentC.dvi
	${DVIPDF} concurrentC.dvi

concurrentC.ps: concurrentC.dvi
	${DVIPS} concurrentC.dvi -o concurrentC.ps
