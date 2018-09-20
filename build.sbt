ThisBuild / scalaVersion := "2.12.6"
ThisBuild / organization := "Innuce"

lazy val cnf = (project in file("."))
  .settings(
    name := "cnf",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % Test,
  )

scalacOptions ++= Seq("-deprecation", "-feature", "-language:postfixOps")


