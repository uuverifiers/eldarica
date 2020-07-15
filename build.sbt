
lazy val commonSettings = Seq(
    name := "Eldarica",
    organization := "uuverifiers",
    version := "2.0.4",
    homepage := Some(url("https://github.com/uuverifiers/eldarica")),
    licenses := Seq("BSD License 2.0" -> url("https://github.com/uuverifiers/eldarica/blob/master/LICENSE")),
    scalaVersion := "2.11.12",
    crossScalaVersions := Seq("2.11.12", "2.12.10"),
    fork in run := true,
    cancelable in Global := true,
    publishTo := Some(Resolver.file("file",  new File( "/home/wv/public_html/maven/" )) )
)

// Jar files for the parsers

lazy val parserSettings = Seq(
    publishArtifact in packageDoc := false,
    publishArtifact in packageSrc := false,
    exportJars := true,
    crossPaths := true 
)

// Parser generation

lazy val parserGen = Seq(
  sourceGenerators in Compile += Def.task {
          val outputDir = (sourceManaged in Compile).value / "parser"
          val base = baseDirectory.value
          
          val cacheDir = outputDir / ".cache"

          val parserDir = base / "src" / "lazabs" / "parser"
          val parserOutputDir = outputDir / "normal"
		
          val hornParserDir = base / "src" / "lazabs" / "horn" / "parser"
          val hornParserOutputDir = outputDir / "horn"
		
          // generated Java files
          val lexerFile =  parserOutputDir / "Lexer.java"
          val hornLexerFile =  hornParserOutputDir / "HornLexer.java"
		
          val parserFile = parserOutputDir / "Parser.java"
          val hornParserFile = hornParserOutputDir / "Parser.java"
		
          val symFile = parserOutputDir / "Symbols.java"
          val hornSymFile = hornParserOutputDir / "Symbols.java"
		
          // grammar file
          val flex = parserDir / "Lexer.jflex"
          val hornFlex = hornParserDir / "HornLexer.jflex"
		
          val cup =  parserDir / "Parser.cup"
          val hornCup =  hornParserDir / "HornParser.cup"
		
          val jflexLib = "./tools/JFlex.jar"
          val cupLib = "./tools/java-cup-11a.jar"

          val cache = FileFunction.cached(cacheDir,
                                          inStyle = FilesInfo.lastModified,
                                          outStyle = FilesInfo.exists){ _ =>
            scala.sys.process.Process(
              "java -jar " + jflexLib + " -d " +
              hornParserOutputDir + " --nobak " + hornFlex).!
            scala.sys.process.Process(
              "java -cp ./tools/ -jar " + cupLib + " -destdir " +
              hornParserOutputDir + " -parser Parser -symbols Symbols " +
              hornCup).!
            scala.sys.process.Process(
              "java -jar " + jflexLib + " -d " + parserOutputDir +
              " --nobak " + flex).!
            scala.sys.process.Process(
              "java -cp ./tools/ -jar " + cupLib + " -destdir " +
              parserOutputDir + " -parser Parser -symbols Symbols " + cup).!
            Set(lexerFile,
                parserFile,
                symFile,
                hornLexerFile,
                hornParserFile,
                hornSymFile)
          }

          cache(Set(hornFlex, hornCup, flex, cup)).toSeq
        }.taskValue
)

lazy val ccParser = (project in file("cc-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "Eldarica-CC-parser",
    packageBin in Compile := baseDirectory.value / "cc-parser.jar"
  ).
  disablePlugins(AssemblyPlugin)

lazy val tplspecParser = (project in file("template-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "Eldarica-tplspec-parser",
    packageBin in Compile := baseDirectory.value / "tplspec-parser.jar"
  ).
  disablePlugins(AssemblyPlugin)

// Actual project

lazy val root = (project in file(".")).
    aggregate(ccParser, tplspecParser).
    dependsOn(ccParser, tplspecParser).
    settings(parserGen: _*).
    settings(commonSettings: _*).
//
    settings(
      scalaSource in Compile := baseDirectory.value / "src",
//
      mainClass in Compile := Some("lazabs.Main"),
//
      unmanagedJars in Compile ++= (baseDirectory map { base =>
        val baseDirectories = (base / "flata")
        val customJars = (baseDirectories ** "*.jar")
        customJars.classpath
      }).value,
//
    scalacOptions in Compile ++=
      List("-feature",
           "-language:implicitConversions,postfixOps,reflectiveCalls"),
    scalacOptions += (scalaVersion map { sv => sv match {
      case "2.11.12" => "-optimise"
      case "2.12.10" => "-opt:_"
    }}).value,	
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a",
//
    libraryDependencies +=
      "org.antlr" % "antlr" % "3.3",
//
    libraryDependencies +=
      "org.scala-lang.modules" % "scala-xml_2.11" % "1.0.5",
//
    resolvers += "uuverifiers" at "http://logicrunch.research.it.uu.se/maven/",
//    libraryDependencies += "uuverifiers" %% "princess" % "2020-07-13"
    libraryDependencies += "uuverifiers" %% "princess" % "nightly-SNAPSHOT"
)
//
