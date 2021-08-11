package dotty
package tools
package vulpix

import java.io.File

import scala.util.Properties.isJavaAtLeast

object TestConfiguration {

  val noCheckOptions = Array(
    "-pagewidth", "120",
    "-color:never",
    "-Xtarget", if isJavaAtLeast("9") then "9" else "8"
  )

  val checkOptions = Array(
    // "-Yscala2-unpickler", s"${Properties.scalaLibrary}",
    "-Yno-deep-subtypes",
    "-Yno-double-bindings",
    "-Yforce-sbt-phases",
    "-Xsemanticdb",
    "-Xverify-signatures"
  )

  val basicClasspath = mkClasspath(List(
    Properties.scalaLibrary,
    Properties.dottyLibrary
  ))

  val withCompilerClasspath = mkClasspath(List(
    Properties.scalaLibrary,
    Properties.scalaAsm,
    Properties.jlineTerminal,
    Properties.jlineReader,
    Properties.compilerInterface,
    Properties.dottyInterfaces,
    Properties.dottyLibrary,
    Properties.tastyCore,
    Properties.dottyCompiler
  ))

  def mkClasspath(classpaths: List[String]): String =
    classpaths.map({ p =>
      val file = new java.io.File(p)
      assert(file.exists, s"File $p couldn't be found.")
      file.getAbsolutePath
    }).mkString(File.pathSeparator)

  val yCheckOptions = Array("-Ycheck:all")

  val commonOptions = Array("-indent", "-language:postfixOps") ++ checkOptions ++ noCheckOptions ++ yCheckOptions
  val defaultOptions = TestFlags(basicClasspath, commonOptions)
  val unindentOptions = TestFlags(basicClasspath, Array("-no-indent") ++ checkOptions ++ noCheckOptions ++ yCheckOptions)
  val allowDeepSubtypes = defaultOptions without "-Yno-deep-subtypes"
  val picklingOptions = defaultOptions and (
    "-Xprint-types",
    "-Ytest-pickler",
    "-Yprint-pos",
    "-Yprint-pos-syms"
  )
  val picklingWithCompilerOptions = picklingOptions.withCompileAndRunClasspath(withCompilerClasspath)
}
