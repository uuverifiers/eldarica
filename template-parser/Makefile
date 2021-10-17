
JLEX_PATH:=/usr/share/java/JLex.jar
JAVA_CUP_PATH:=../cc-parser/lib/java-cup-11a.jar

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

all: tplspec-parser.jar lazabs/horn/abstractions/TplSpec/Test.class


tplspec-parser.jar: $(PARSER_BINDIR) $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Absyn/TplSpec.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/sym.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Yylex.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/PrettyPrinterNonStatic.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/parser.class
	cd $(PARSER_BINDIR) && jar cf $(PARSER_BASEDIR)/tplspec-parser.jar lazabs


$(PARSER_BINDIR):
	mkdir $(PARSER_BINDIR)

clean:
#	rm -rf parser.jar
	rm -rf $(PARSER_BINDIR)
	rm -rf TplSpec
	rm -rf TplSpec.tex TplSpec.dvi TplSpec.aux TplSpec.log TplSpec.ps


# just any of the files that is created by bnfc
TplSpec.tex: TplSpec.cf
	bnfc -p lazabs.horn.abstractions -java1.5 TplSpec.cf

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Absyn/TplSpec.java: TplSpec.cf
	bnfc -p lazabs.horn.abstractions -java1.5 TplSpec.cf

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Absyn/TplSpec.class: $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Absyn/TplSpec.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/abstractions/TplSpec/Absyn/*.java

lazabs/horn/abstractions/TplSpec/Yylex.java: lazabs/horn/abstractions/TplSpec/Yylex
#       remove some quotes that JLex does not accept
	sed 's/\\\^/\^/g' <lazabs/horn/abstractions/TplSpec/Yylex >lazabs/horn/abstractions/TplSpec/Yylex.temp
	mv lazabs/horn/abstractions/TplSpec/Yylex.temp lazabs/horn/abstractions/TplSpec/Yylex
#       quote dashes "-"
	sed 's/\\\+-/\\+\\-/g' <lazabs/horn/abstractions/TplSpec/Yylex >lazabs/horn/abstractions/TplSpec/Yylex.temp
	mv lazabs/horn/abstractions/TplSpec/Yylex.temp lazabs/horn/abstractions/TplSpec/Yylex
	${JAVA} ${JAVA_FLAGS} ${JLEX} lazabs/horn/abstractions/TplSpec/Yylex

lazabs/horn/abstractions/TplSpec/sym.java lazabs/horn/abstractions/TplSpec/parser.java: lazabs/horn/abstractions/TplSpec/TplSpec.cup
	${JAVA} ${JAVA_FLAGS} ${CUP} ${CUPFLAGS} lazabs/horn/abstractions/TplSpec/TplSpec.cup
	mv sym.java parser.java lazabs/horn/abstractions/TplSpec/

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Yylex.class: lazabs/horn/abstractions/TplSpec/Yylex.java lazabs/horn/abstractions/TplSpec/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/abstractions/TplSpec/Yylex.java

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/sym.class: lazabs/horn/abstractions/TplSpec/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/abstractions/TplSpec/sym.java

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/parser.class: lazabs/horn/abstractions/TplSpec/parser.java lazabs/horn/abstractions/TplSpec/sym.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/abstractions/TplSpec/parser.java

lazabs/horn/abstractions/TplSpec/PrettyPrinterNonStatic.java: lazabs/horn/abstractions/TplSpec/PrettyPrinter.java
	sed 's/PrettyPrinter/PrettyPrinterNonStatic/g' <lazabs/horn/abstractions/TplSpec/PrettyPrinter.java | sed 's/static//g' >lazabs/horn/abstractions/TplSpec/PrettyPrinterNonStatic.java

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/PrettyPrinter.class: lazabs/horn/abstractions/TplSpec/PrettyPrinter.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/abstractions/TplSpec/PrettyPrinter.java

$(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/PrettyPrinterNonStatic.class: lazabs/horn/abstractions/TplSpec/PrettyPrinterNonStatic.java
	${JAVAC} ${JAVAC_FLAGS} -d $(PARSER_BINDIR) lazabs/horn/abstractions/TplSpec/PrettyPrinterNonStatic.java

lazabs/horn/abstractions/TplSpec/Test.class: lazabs/horn/abstractions/TplSpec/Test.java $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/PrettyPrinter.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/Yylex.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/parser.class $(PARSER_BINDIR)/lazabs/horn/abstractions/TplSpec/sym.class
	${JAVAC} ${JAVAC_FLAGS} lazabs/horn/abstractions/TplSpec/Test.java

TplSpec.dvi: TplSpec.tex
	${LATEX} TplSpec.tex

TplSpec.pdf: TplSpec.dvi
	${DVIPDF} TplSpec.dvi

TplSpec.ps: TplSpec.dvi
	${DVIPS} TplSpec.dvi -o TplSpec.ps
