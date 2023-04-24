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

package lazabs.upp.parser

import scala.util.parsing.combinator.syntactical._
import lazabs.ast.ASTree._
import lazabs.types._

object UppCParser extends StandardTokenParsers {
  lexical.delimiters ++= List("(",")","{","}","[","]","==","=",":=","-=","+=","++","--","&&","||","!","<","<=",">",">=","+","-","*",",",";")
  lexical.reserved += ("while","if","else","typedef","const","Int","true","false")
  
  /**
   * the size of arrays
  */
  val arraySize = collection.mutable.Map[String,Expression]().empty
  /**
   * constants
   */
  val constants = collection.mutable.Map[String,NumericalConst]().empty
  
  def constant = numericLit ^^ { num => NumericalConst(num.toInt) }
  
  def identifier = ident ^^ { s =>
    Variable("upp_" + s).stype(IntegerType()) 
  }
  
  def declarations: Parser[List[Declaration]] = (declaration ~ rep(declaration)) ^^ {
    case first ~ rest => first ++ rest.flatten
  }
  
  def declaration: Parser[List[Declaration]] = (varDecl | funDecl | typeDecl | constDecl)
  
  def identList: Parser[List[String]] = (ident ~ rep("," ~> ident)) ^^ {
    case first ~ rest => first :: rest
  }  

  def varDecl: Parser[List[VarDeclaration]] = 
    (typeSpec ~ identList <~ ";") ^^ {
      case x ~ vList => vList.map(v => VarDeclaration("upp_" + v, x, NumericalConst(0))) 
    } |
    (typeSpec ~ identList ~ "=" ~ integerExpr <~ ";") ^^ {
      case x ~ vList ~ "=" ~ value => vList.map(v => VarDeclaration("upp_" + v, x, value))
    } |
    (typeSpec ~ identList ~ "[" ~ integerExpr ~ "]" <~ ";") ^^ {
      case x ~ vList ~ "[" ~ size ~ "]" =>
        vList.map{v =>
          arraySize += (("upp_" + v) -> size)
          VarDeclaration("upp_" + v, ArrayType(IntegerType()), ScArray(None, Some(size)))
        }
    }

  def funDecl: Parser[List[Declaration]] = (typeSpec ~ ident ~ "(" ~ rep(paramType) ~ ")" ~ statement) ^^ {
    case typ ~ name ~ "(" ~ params ~ ")" ~ st => 
      List(FunctionDefinition("upp_" + name, params.map(x => Parameter("upp_" + x._1,x._2)), typ, st))
  }

  def typeDecl: Parser[List[Declaration]] = ("typedef" ~> typeSpec ~ ident <~ ";") ^^ {
    case typ ~ name => 
      List()
  }
  
  def constDecl: Parser[List[Declaration]] = ("const" ~> typeSpec ~ ident ~ "=" ~ constant <~ ";") ^^ {
    case typ ~ name ~ "=" ~ value =>
      constants += (("upp_" + name) -> value)
      List(ConstDeclaration("upp_" + name, typ, value))
  }

  def statement: Parser[Expression] = (
       compoundStmt
    |  assignment <~ ";"
    |  integerExpr <~ ";"
    |  iterationStmt
  )
  
  def compoundStmt: Parser[Expression] = "{" ~> stmtList <~ "}" ^^ {
    case declList =>
      Block(declList)
  }
  
  def iterationStmt: Parser[Expression] = "while" ~ "(" ~> booleanExpr ~ ")" ~ statement ^^ {
    case (cond ~ ")" ~ body) => WhileLoop(cond, body) 
  }

  def stmtList: Parser[List[ASTree]] = rep(statement | varDecl) ^^ {
    case s =>
      s.map{_ match {
        case se if (se.isInstanceOf[Expression]) => List[ASTree](se.asInstanceOf[Expression])
        case se => se.asInstanceOf[List[ASTree]]
      }}.flatten
  }

  def paramType: Parser[(String,Type)] = (typeSpec ~ ident) ^^ {
    case x ~ y => (y,x)
  }

  def typeSpec: Parser[Type] = ((ident ~ opt("[" ~ integerExpr ~ "," ~ integerExpr ~ "]")) ^^ { 
    case "chan" ~ _ => ClassType("chan")
    case "clock" ~ _ => ClassType("clock")
    case "int" ~ Some("[" ~ l ~ "," ~ h ~ "]") => IntegerType() // approximation of bounded variables 
    case "int" ~ None => IntegerType()
    case "void" ~ _ => UnitType()
    case t ~ _ => ClassType(t)
    case un@_ => throw new Exception("Unrecognized type " + un)
  })

  //##########################################################
  //#####                   Expressions                  #####                 
  //##########################################################
  
  def variable: Parser[Expression] = identifier ~ opt("[" ~ integerExpr ~ "]") ^^ {
    case (id ~ None) => constants.get(id.name) match {
      case Some(constant) => constant
      case None => id
    }
    case (id ~ Some("[" ~ index ~ "]")) =>
      ArraySelect(ScArray(Some(id),arraySize.get(id.name)),index)
  }
  
  
  def integerExpr: Parser[Expression] = (integerTerm ~ rep("+" ~ integerTerm | "-" ~ integerTerm)) ^^ {
    case first ~ rest => rest.foldLeft(first) {
      case (NumericalConst(x), "+" ~ NumericalConst(y)) => NumericalConst(x + y)
      case (NumericalConst(x), "-" ~ NumericalConst(y)) => NumericalConst(x - y)
      case (x, "+" ~ y) => Addition(x,y)
      case (x, "-" ~ y) => Subtraction(x,y)
    }
  }

  def integerTerm: Parser[Expression] = (integerFactor ~ rep("*" ~ integerFactor | "/" ~ integerFactor)) ^^ {
    case first ~ rest => rest.foldLeft(first) {
      case (x, "*" ~ y) => Multiplication(x,y)
    }
  }
  
  def integerFactor: Parser[Expression] = 
    ( constant |
      (variable ~ opt("++")) ^^ {
        case (v ~ None) => v
        case (v ~ Some(_)) => Addition(v,NumericalConst(1))
      } |
      ("(" ~> integerExpr <~ ")" ) |
      ("-" ~> integerFactor) ^^ {
        case f => Minus(f)
      }
  )

  def booleanExpr: Parser[Expression] = (booleanTerm ~ rep("||" ~ booleanTerm)) ^^ {
    case first ~ rest => rest.foldLeft(first) {
      case (x, "||" ~ y) => Disjunction(x,y)
    }
  }
  
  def booleanTerm: Parser[Expression] = (booleanFactor ~ rep("&&" ~ booleanFactor)) ^^ {
    case first ~ rest => rest.foldLeft(first) {
      case (x, "&&" ~ y) => Conjunction(x,y)
    }
  }
  
  def booleanFactor: Parser[Expression] = 
    ("(" ~> booleanExpr <~ ")" ) |
    (integerExpr ~ ">" ~ integerExpr) ^^ {
      case left ~ ">" ~ right =>
        GreaterThan(left, right)
    } |
    (integerExpr ~ ">=" ~ integerExpr) ^^ {
      case left ~ ">=" ~ right =>
        GreaterThanEqual(left, right)
    } |
    (integerExpr ~ "<" ~ integerExpr) ^^ {
      case left ~ "<" ~ right =>
        LessThan(left, right)
    } |
    (integerExpr ~ "<=" ~ integerExpr) ^^ {
      case left ~ "<=" ~ right =>
        LessThanEqual(left, right)
    } |
    (integerExpr ~ "==" ~ integerExpr) ^^ {
      case left ~ "==" ~ right =>
        Equality(left, right)
    } |
    ("!" ~> booleanFactor) ^^ {
      case f => Not(f)
    }
  
  def assignmentList: Parser[List[Expression]] = (assignment ~ rep("," ~> assignment)) ^^ {
    case first ~ rest => first :: rest
  }
  
  def call: Parser[FunctionCall] = ident ~ "(" ~ argList ~ ")" ^^ {
    case (funcName ~ "(" ~ exprList ~ ")") => FunctionCall("upp_" + funcName, exprList)
  }
  
  def assignAction: Parser[Either[List[Expression],FunctionCall]] = (
    assignmentList ^^ {case aList => Left(aList)} 
    | 
    call ^^ {case c => Right(c)}
  )
  
  def argList: Parser[List[Expression]] = (opt(integerExpr) ~ rep("," ~ integerExpr)) ^^ {
    case None ~ Nil => List()
    case Some(arg) ~ rest => arg :: rest.map {
      case ("," ~ y) => y
    }
  }
  
  def assignment: Parser[Expression] = (variable ~ (":=" | "=" | "+=" | "-=") ~ integerExpr) ^^ { 
    case left ~ (":=" | "=") ~ right =>
      Assignment(left, right)
    case left ~ ("+=") ~ right =>
      Assignment(left, Addition(left,right))
    case left ~ ("-=") ~ right =>
      Assignment(left, Subtraction(left,right))
  }
  
  def parseAssignAction(orig: String): Either[List[Expression],FunctionCall] = {
    val s = stripBlockComment(stripLineComment(orig))
    val tokens = new lexical.Scanner(s)
    phrase(assignAction)(tokens) match {
      case Success(tree, _) => tree
      case e: NoSuccess =>
        throw new IllegalArgumentException("Syntax error in Assignment declaration: " + s)
    }
  }
  
  def parseBooleanExpr(orig: String): Expression = {
    val s = stripBlockComment(stripLineComment(orig))
    val tokens = new lexical.Scanner(s)
    phrase(booleanExpr)(tokens) match {
      case Success(tree, _) => tree
      case e: NoSuccess =>
        throw new IllegalArgumentException("Syntax error in Boolean declaration: " + s)
    }
  }
  
  def apply(orig:String): List[Declaration] = {
    val s = stripBlockComment(stripLineComment(orig)) 
    if(s.trim == "") return List()
    val tokens = new lexical.Scanner(s)
    phrase(declarations)(tokens) match {
      case Success(tree, _) => tree
      case e: NoSuccess =>
        throw new IllegalArgumentException("Syntax error in Uppaal declaration: " + s)
      }
  }
  
  def stripLineComment(s: String) = s.replaceAll("//(.*?)\\r?\\n","")
  def stripBlockComment(s: String) = s.replaceAll("/\\*(?:.|[\\n\\r])*?\\*/","")
}