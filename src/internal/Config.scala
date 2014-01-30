package scala.virtualization.lms
package internal

trait Config {
  val verbosity = System.getProperty("lms.verbosity","0").toInt
  val sourceinfo = System.getProperty("lms.sourceinfo","0").toInt
  val addControlDeps = System.getProperty("lms.controldeps","true").toBoolean
  
  //Config for using c++ target shared pointer
  val cppUseSharedPtr = System.getProperty("lms.cpp.use.sharedptr","true").toBoolean
}
