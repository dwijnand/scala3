package dotty.tools
package dotc
package config

import scala.annotation.internal.sharable

import java.io.IOException
import java.util.jar.Attributes.{ Name => AttributeName }
import java.nio.charset.StandardCharsets

/** Loads `compiler.properties` from the jar. */
object Properties extends PropertiesTrait {
  protected def propCategory: String = "compiler"
  protected def pickJarBasedOn: Class[PropertiesTrait] = classOf[PropertiesTrait]

  /** Scala manifest attributes.
   */
  @sharable val ScalaCompilerVersion: AttributeName = new AttributeName("Scala-Compiler-Version")
}

trait PropertiesTrait {
  protected def propCategory: String      // specializes the remainder of the values
  protected def pickJarBasedOn: Class[?]  // props file comes from jar containing this

  /** The name of the properties file */
  protected val propFilename: String = "/" + propCategory + ".properties"

  /** The loaded properties */
  @sharable protected lazy val scalaProps: java.util.Properties = {
    val props = new java.util.Properties
    val stream = pickJarBasedOn getResourceAsStream propFilename
    if (stream ne null)
      quietlyDispose(props load stream, stream.close)

    props
  }

  private def quietlyDispose(action: => Unit, disposal: => Unit) =
    try     { action }
    finally
        try     { disposal }
        catch   { case _: IOException => }

  def propIsSet(name: String): Boolean                  = System.getProperty(name) != null
  def propIsSetTo(name: String, value: String): Boolean = propOrNull(name) == value
  def propOrElse(name: String, alt: => String): String  = Option(System.getProperty(name)).getOrElse(alt)
  def propOrEmpty(name: String): String                 = propOrElse(name, "")
  def propOrNull(name: String): String                  = propOrElse(name, null)
  def propOrNone(name: String): Option[String]          = Option(propOrNull(name))
  def propOrFalse(name: String): Boolean                = propOrNone(name) exists (x => List("yes", "on", "true") contains x.toLowerCase)
  def setProp(name: String, value: String): String      = System.setProperty(name, value)
  def clearProp(name: String): String                   = System.clearProperty(name)

  def envOrElse(name: String, alt: => String): String   = Option(System getenv name) getOrElse alt
  def envOrNone(name: String): Option[String]           = Option(System getenv name)

  // for values based on propFilename, falling back to System properties
  def scalaPropOrElse(name: String, alt: => String): String = scalaPropOrNone(name).getOrElse(alt)
  def scalaPropOrEmpty(name: String): String                = scalaPropOrElse(name, "")
  def scalaPropOrNone(name: String): Option[String]         = Option(scalaProps.getProperty(name)).orElse(propOrNone("scala." + name))

  /** Either the development or release version if known, otherwise
   *  the empty string.
   */
  def versionNumberString: String = scalaPropOrEmpty("version.number")

  /** The version number of the jar this was loaded from,
   *  or `"(unknown)"` if it cannot be determined.
   */
  val simpleVersionString: String = {
    val v = scalaPropOrElse("version.number", "(unknown)")
    v + (
      if (v.contains("SNAPSHOT") || v.contains("NIGHTLY"))
        "-git-" + scalaPropOrElse("git.hash", "(unknown)")
      else
        ""
    )
  }

  /** The version number of the jar this was loaded from plus `"version "` prefix,
   *  or `"version (unknown)"` if it cannot be determined.
   */
  val versionString: String = "version " + simpleVersionString

  /** Whether the current version of compiler is experimental
   *
   *  1. Snapshot, nightly releases and non-bootstrapped compiler are experimental.
   *  2. Features supported by experimental versions of the compiler:
   *     - research plugins
   */
  val experimental: Boolean = versionString.contains("SNAPSHOT") || versionString.contains("NIGHTLY") || versionString.contains("nonbootstrapped")

  val copyrightString: String = scalaPropOrElse("copyright.string", "Copyright 2002-2021, LAMP/EPFL and Lightbend, Inc.")

  /** This is the encoding to use reading in source files, overridden with -encoding.
   *  Note that it uses "prop" i.e. looks in the scala jar, not the system properties.
   */
  def sourceEncoding: String        = scalaPropOrElse("file.encoding", StandardCharsets.UTF_8.name)
  def sourceReader: String          = scalaPropOrElse("source.reader", "scala.tools.nsc.io.SourceReader")

  /** This is the default text encoding, overridden (unreliably) with
   *  `JAVA_OPTS="-Dfile.encoding=Foo"`
   */
  def encodingString: String        = propOrElse("file.encoding", StandardCharsets.UTF_8.name)

  /** The default end of line character.
   */
  def lineSeparator: String         = System.lineSeparator()

  /** Various well-known properties.  */
  def javaClassPath: String         = propOrEmpty("java.class.path")
  def javaHome: String              = propOrEmpty("java.home")
  def javaVendor: String            = propOrEmpty("java.vendor")
  def javaVersion: String           = propOrEmpty("java.version")
  def javaVmInfo: String            = propOrEmpty("java.vm.info")
  def javaVmName: String            = propOrEmpty("java.vm.name")
  def javaVmVendor: String          = propOrEmpty("java.vm.vendor")
  def javaVmVersion: String         = propOrEmpty("java.vm.version")
  def javaSpecVersion: String       = propOrEmpty("java.specification.version")
  def javaSpecVendor: String        = propOrEmpty("java.specification.vendor")
  def javaSpecName: String          = propOrEmpty("java.specification.name")
  def jdkHome: String               = envOrElse("JDK_HOME", envOrElse("JAVA_HOME", javaHome))
  def osName: String                = propOrEmpty("os.name")
  def scalaHome: String             = propOrEmpty("scala.home")
  def tmpDir: String                = propOrEmpty("java.io.tmpdir")
  def userDir: String               = propOrEmpty("user.dir")
  def userHome: String              = propOrEmpty("user.home")
  def userName: String              = propOrEmpty("user.name")

  /** Some derived values.  */
  /** Returns `true` iff the underlying operating system is a version of Microsoft Windows. */
  def isWin: Boolean                = osName startsWith "Windows"
  // See https://mail.openjdk.java.net/pipermail/macosx-port-dev/2012-November/005148.html for
  // the reason why we don't follow developer.apple.com/library/mac/#technotes/tn2002/tn2110.
  /** Returns `true` iff the underlying operating system is a version of Apple Mac OSX.  */
  def isMac: Boolean                 = osName startsWith "Mac OS X"
  /** Returns `true` iff the underlying operating system is a Linux distribution. */
  def isLinux               = osName startsWith "Linux"

  def coloredOutputEnabled: Boolean = propOrElse("scala.color", "auto") match {
    case "auto" => System.console() != null && !isWin
    case s      => s == "" || "true".equalsIgnoreCase(s)
  }

  def versionMsg: String            = s"Scala $propCategory $versionString -- $copyrightString"
  def scalaCmd: String              = if (isWin) "scala.bat" else "scala"
  def scalacCmd: String             = if (isWin) "scalac.bat" else "scalac"
}
