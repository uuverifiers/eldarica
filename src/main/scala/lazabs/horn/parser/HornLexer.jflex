/**
 * Copyright (c) 2011-2014 Hossein Hojjat. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.parser;
import java_cup.runtime.*;
import java.math.BigInteger;


%%

%class HornLexer
%cupsym Symbols
%unicode
%line
%column
%public
%apiprivate

%cup

%eofval{
  return symbol(Symbols.EOF);
%eofval}

%{
    private Symbol symbol(int type) {
        return new Symbol(type, yyline, yycolumn);
    }

    private Symbol symbol(int type, Object value) {
        return new Symbol(type, yyline, yycolumn, value);
    }
    
    public int getLine() { return  yyline; }
    public int getColumn() {return yycolumn; }
%}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
WhiteSpace     = [ \t\f] | {LineTerminator}

Sign           = "+" | "-"
IntLiteral     = (0 | [1-9][0-9]*)
Identifier     = [a-zA-Z][a-zA-Z0-9_']* 

Comment = {TraditionalComment} | {EndOfLineComment} | {ArmcComment}

TraditionalComment   = "/*" [^*:] ~"*/" | "/*" "*"+ "/"
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}
ArmcComment     = "%" {InputCharacter}* {LineTerminator}


%%

<YYINITIAL> {
  ","           { return symbol(Symbols.COMMA); } 
  ";"           { return symbol(Symbols.OR); } 
  "\\" + "+"    { return symbol(Symbols.NOT); }
  "+"           { return symbol(Symbols.PLUS); }
  "*"           { return symbol(Symbols.TIMES); } 
  "mod"         { return symbol(Symbols.MOD); }  
  "-"           { return symbol(Symbols.MINUS); }
  "_"           { return symbol(Symbols.UNDERLINE); }
  "/"           { return symbol(Symbols.DIV); }
  "=<"          { return symbol(Symbols.LEQ); }  
  "<"           { return symbol(Symbols.LT); }
  ">="          { return symbol(Symbols.GEQ); }
  ">"           { return symbol(Symbols.GT); }
  "="           { return symbol(Symbols.EQ); }
  "!="          { return symbol(Symbols.NEQ); }
  "=\\="        { return symbol(Symbols.NEQ); }
  ":-"          { return symbol(Symbols.IF); }  
  "."           { return symbol(Symbols.DOT); }
  "("           { return symbol(Symbols.LPAREN); }
  ")"           { return symbol(Symbols.RPAREN); }
  "-["          { return symbol(Symbols.ARMC_PARAMS_S); }
  "]"           { return symbol(Symbols.ARMC_PARAMS_E); }
  "false"       { return symbol(Symbols.FALSE); }
  {IntLiteral}  { return symbol(Symbols.NUMBER, new BigInteger(yytext())); }
  {Identifier}  { return symbol(Symbols.ID, new String(yytext())); } 
  {WhiteSpace}  { /* skip */ }
  {Comment}	{ /* skip */ }
  
}


[^] | \n          { System.err.println("Illegal character '" + yytext() + "'" + " Scala Lexial Analyzer in " + yyline + " " + yycolumn); }
