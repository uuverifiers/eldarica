
JLEX_PATH:=/usr/share/java/JLex.jar
JAVA_CUP_PATH:=../lib/java-cup-11a.jar

JAVAC:=javac
JAVAC_FLAGS:=-target 1.5

JAVA:=java
JAVA_FLAGS:=

# enough memory for the compiler on 64-bit architectures
JAVA_OPTS=-Xmx1G


CUP = java_cup.Main
CUPFLAGS = -nopositions -expect 100

JLEX = JLex.Main

LATEX = latex
DVIPS = dvips
DVIPDF = dvipdfm


PARSER_BASEDIR=$(shell pwd)
PARSER_BINDIR=$(PARSER_BASEDIR)/bin


CLASSPATH:=$(CLASSPATH):$(PARSER_BASEDIR):$(JLEX_PATH):$(JAVA_CUP_PATH)
export CLASSPATH

all: tplspec-parser.jar TplSpec/Test.class


tplspec-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/TplSpec/Absyn/TplSpec.class $(PARSER_BINDIR)/TplSpec/sym.class $(PARSER_BINDIR)/TplSpec/Yylex.class $(PARSER_BINDIR)/TplSpec/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/TplSpec/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/tplspec-parser.jar TplSpec


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf TplSpec
	rm -rf TplSpec.tex TplSpec.dvi TplSpec.aux TplSpec.log TplSpec.ps


# just any of the files that is created by bnfc
TplSpec.tex: TplSpec.cf
	bnfc -java1.5 TplSpec.cf

$(PARSER_BINDIR)/TplSpec/Absyn/TplSpec.java: TplSpec.cf
	bnfc -java1.5 TplSpec.cf

$(PARSER_BINDIR)/TplSpec/Absyn/TplSpec.class: $(PARSER_BINDIR)/TplSpec/Absyn/TplSpec.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) TplSpec/Absyn/*.java

TplSpec/Yylex.java: TplSpec/Yylex
#       remove some quotes that JLex does not accept
	sed 's/\\\^/\^/g' <TplSpec/Yylex >TplSpec/Yylex.temp
	mv TplSpec/Yylex.temp TplSpec/Yylex
#       quote dashes "-"
	sed 's/\\\+-/\\+\\-/g' <TplSpec/Yylex >TplSpec/Yylex.temp
	mv TplSpec/Yylex.temp TplSpec/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} TplSpec/Yylex

TplSpec/sym.java TplSpec/parser.java: TplSpec/TplSpec.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} TplSpec/TplSpec.cup
	mv sym.java parser.java TplSpec/

$(PARSER_BINDIR)/TplSpec/Yylex.class: TplSpec/Yylex.java TplSpec/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) TplSpec/Yylex.java

$(PARSER_BINDIR)/TplSpec/sym.class: TplSpec/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) TplSpec/sym.java

$(PARSER_BINDIR)/TplSpec/parser.class: TplSpec/parser.java TplSpec/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) TplSpec/parser.java

TplSpec/PrettyPrinterNonStatic.java: TplSpec/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <TplSpec/PrettyPrinter.java | sed 's/static//g' >TplSpec/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/TplSpec/PrettyPrinter.class: TplSpec/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) TplSpec/PrettyPrinter.java

$(PARSER_BINDIR)/TplSpec/PrettyPrinterNonStatic.class: TplSpec/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) TplSpec/PrettyPrinterNonStatic.java

TplSpec/Test.class: TplSpec/Test.java $(PARSER_BINDIR)/TplSpec/PrettyPrinter.class $(PARSER_BINDIR)/TplSpec/Yylex.class $(PARSER_BINDIR)/TplSpec/parser.class $(PARSER_BINDIR)/TplSpec/sym.class
	${JAVAC} ${JAVAC_FLAGS} TplSpec/Test.java

TplSpec.dvi: TplSpec.tex
	${LATEX} TplSpec.tex

TplSpec.pdf: TplSpec.dvi
	${DVIPDF} TplSpec.dvi

TplSpec.ps: TplSpec.dvi
	${DVIPS} TplSpec.dvi -o TplSpec.ps
