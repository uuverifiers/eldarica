
lazy val commonSettings = Seq(
    name := "Eldarica",
    organization := "uuverifiers",
    version := "2.1",
    homepage := Some(url("https://github.com/uuverifiers/eldarica")),
    licenses := Seq("BSD License 2.0" -> url("https://github.com/uuverifiers/eldarica/blob/master/LICENSE")),
    scmInfo              := Some(ScmInfo(
                                   url("https://github.com/uuverifiers/eldarica"),
                                   "scm:git@github.com/uuverifiers/eldarica.git")),
    developers           := List(
                              Developer(
                                id    = "hhojjat",
                                name  = "Hossein Hojjat",
                                email = "hhojjat@gmail.com",
                                url   = url("https://cs.rit.edu/~hh/")
                              ),
                              Developer(
                                id    = "pruemmer",
                                name  = "Philipp Ruemmer",
                                email = "ph_r@gmx.net",
                                url   = url("https://philipp.ruemmer.org")
                              ),
                              Developer(
                                id    = "zafer.esen",
                                name  = "Zafer Esen",
                                email = "zafer.esen@it.uu.se",
                                url   = url("https://katalog.uu.se/empinfo/?id=N18-2424")
                              ),
                              Developer(
                                id    = "filipkonecny",
                                name  = "Filip Konecny",
                                email = "filipkonecny@gmail.com",
                                url   = url("https://github.com/filipkonecny")
                              ),
                              Developer(
                                id    = "psubotic",
                                name  = "Pavle Subotic",
                                email = "psubotic@gmail.com",
                                url   = url("https://psubotic.github.io/")
                              ),
                              Developer(
                                id    = "sankalpgambhir",
                                name  = "Gambhir Sankalp",
                                email = "sankalp.gambhir@epfl.ch",
                                url   = url("https://sankalp.gambhir.gg/")
                              )
                            ),
    description          := "Eldarica is an SMT solver for systems of Constrained Horn Clauses (CHC).",
    scalaVersion := "2.11.12",
    crossScalaVersions := Seq("2.11.12", "2.12.18"),
    run / fork := true,
    cancelable in Global := true,
    publishTo := Some(Resolver.file("file",  new File( "/home/compilation/public_html/maven/" )) )
)

// Jar files for the parsers

lazy val parserSettings = Seq(
//    packageDoc / publishArtifact := false,
//    packageSrc / publishArtifact := false,
    exportJars := true,
    crossPaths := true
)

// Parser generation

lazy val parserGen = Seq(
  Compile / sourceGenerators += Def.task {
          val outputDir = (Compile / sourceManaged).value / "parser"
          val base = baseDirectory.value

          val cacheDir = outputDir / ".cache"

          val parserDir = base / "src" / "main" / "scala" / "lazabs" / "parser"
          val parserOutputDir = outputDir / "normal"

          val hornParserDir = base / "src" / "main" / "scala" / "lazabs" / "horn" / "parser"
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
    Compile / packageBin := baseDirectory.value / "cc-parser.jar",
    Compile / unmanagedJars += baseDirectory.value / "cc-parser.jar"
  ).
  disablePlugins(AssemblyPlugin)

lazy val tplspecParser = (project in file("template-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "Eldarica-tplspec-parser",
    Compile / packageBin := baseDirectory.value / "tplspec-parser.jar",
    Compile / unmanagedJars += baseDirectory.value / "tplspec-parser.jar"
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
      Compile / mainClass := Some("lazabs.Main"),
//
      Compile / unmanagedJars ++= (baseDirectory map { base =>
        val baseDirectories = (base / "flata")
        val customJars = (baseDirectories ** "*.jar")
        customJars.classpath
      }).value,
//
    Compile / scalacOptions ++=
      List("-feature",
           "-language:implicitConversions,postfixOps,reflectiveCalls",
           "-encoding", "UTF-8"),
    scalacOptions += (scalaVersion map { sv => sv match {
      case "2.11.12" => "-optimise"
      case "2.12.18" => "-opt:_"
    }}).value,
//
    assembly / test := None,
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a",
//
    libraryDependencies +=
      "org.antlr" % "antlr" % "3.3",
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-xml" % "1.3.0",
//
    libraryDependencies +=
      "org.scalactic" %% "scalactic" % "3.2.14",
//
    libraryDependencies +=
      "org.scalatest" %% "scalatest" % "3.2.14" % "test",
//
//    libraryDependencies += "io.github.uuverifiers" %% "princess" % "2024-03-22"
//
    resolvers += "uuverifiers" at "https://eldarica.org/maven/",
    libraryDependencies += "uuverifiers" %% "princess" % "nightly-SNAPSHOT"

)
//
