import sbt._
import java.io.File

object LMSBuild extends Build {
  // FIXME: custom-built scalatest
  val dropboxScalaTestRepo = "Dropbox" at "http://dl.dropbox.com/u/12870350/scala-virtualized"
  
  val prereleaseScalaTest = "XXX" at "https://oss.sonatype.org/content/groups/public" // "org/scalatest/scalatest_2.10.0-M5/1.9-2.10.0-M5-B2/"
  
  //val scalaTest = "org.scalatest" % "scalatest_2.10.0-virtualized-SNAPSHOT" % "1.6.1-SNAPSHOT" % "test"
  //val scalaTest = "org.scalatest" % "scalatest_2.10.0-M7" % "1.9-2.10.0-M7-B1" % "test"
  //val scalaTest = "org.scalatest" % "scalatest_2.10.0-RC1" % "2.0.M4" % "test"  
  val scalaTest = "org.scalatest" % "scalatest_2.10.0" % "2.0.M5" % "test"  
  
  val virtScala = Option(System.getenv("SCALA_VIRTUALIZED_VERSION")).getOrElse("2.10.0")

  lazy val lms = Project("LMS", file("."))
}
