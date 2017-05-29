
lazy val commonSettings = Seq(
    name := "Eldarica-Horn-Solver",
    organization := "uuverifiers",
    version := "2016-12-26",
    scalaVersion := "2.11.8",
    crossScalaVersions := Seq("2.11.8", "2.12.1"),
    publishTo := Some(Resolver.file("file",  new File( "/tmp/shared-repo" )) )
)

// Actual project

lazy val root = (project in file(".")).
  settings(commonSettings: _*).
//
  settings(
    scalaSource in Compile := baseDirectory.value / "src",
//
    mainClass in Compile := Some("Main"),
//
	unmanagedBase := baseDirectory.value / "lib",
//
//	unmanagedBase ++= baseDirectory.value / "flata",	
//
	// exclude any folders 
/*	excludeFilter in Compile := {
		val refine = (baseDirectory.value / "src" / "lazabs" / "refine" ).getCanonicalPath
  		new SimpleFileFilter(f => 
  			(f.getCanonicalPath startsWith refine)  			
  		)
	},
*/
//
    scalacOptions in Compile ++=
      List("-feature",
           "-language:implicitConversions,postfixOps,reflectiveCalls"),
    scalacOptions <+= scalaVersion map { sv => sv match {
      case "2.11.8" => "-optimise"
      case "2.12.1" => "-opt:l:classpath"
    }},
//
    libraryDependencies +=
      "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4",
//
    libraryDependencies +=
      "net.sf.squirrel-sql.thirdparty-non-maven" % "java-cup" % "0.11a")
//
    

//