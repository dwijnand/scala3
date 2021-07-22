package dotty.tools
package dotc
package reporting

import core.Contexts._
import config.Config
import config.Printers
import core.Mode

/** Exposes the {{{ trace("question") { op } }}} syntax.
 *
 * Traced operations will print indented messages if enabled.
 * Tracing depends on [[Config.tracingEnabled]] and [[dotty.tools.dotc.config.ScalaSettings.Ylog]].
 * Tracing can be forced by replacing [[trace]] with [[trace.force]] or [[trace.log]] (see below).
 */
object trace extends TraceSyntax:
  inline def isEnabled = Config.tracingEnabled
  protected val isForced = false

  object force extends TraceSyntax:
    inline def isEnabled: true = true
    protected val isForced = true

  object log extends TraceSyntax:
    inline def isEnabled: true = true
    protected val isForced = false
end trace

/** This module is carefully optimized to give zero overhead if Config.tracingEnabled
 *  is false. The `trace` operation is called in various hotspots, so every tiny bit
 *  of overhead is unacceptable: boxing, closures, additional method calls are all out.
 */
trait TraceSyntax:
  inline def isEnabled: Boolean
  protected val isForced: Boolean

  inline def onDebug[T](inline question: String)(inline op: T)(using Context): T =
    conditionally(ctx.settings.YdebugTrace.value, question, false)(op)

  inline def conditionally[T](inline cond: Boolean, inline question: String, inline show: Boolean)(inline op: T)(using Context): T =
    apply(question, if cond then Printers.default else Printers.noPrinter, show)(op)

  inline def apply[T, U >: T](inline question: String, inline printer: Printers.Printer, inline showOp: U => String)(inline op: T)(using Context): T =
    inline if isEnabled then doTrace(question, printer, showOp)(op) else op

  inline def apply[T](inline question: String, inline printer: Printers.Printer, inline show: Boolean)(inline op: T)(using Context): T =
    apply(question, printer, if show then showShowable(_) else String.valueOf(_: Any))(op)

  inline def apply[T](inline question: String, inline printer: Printers.Printer)(inline op: T)(using Context): T =
    apply(question, printer, false)(op)

  inline def apply[T](inline question: String, inline show: Boolean)(inline op: T)(using Context): T =
    apply(question, Printers.default, show)(op)

  inline def apply[T](inline question: String)(inline op: T)(using Context): T =
    apply(question, false)(op)

  private def showShowable(x: Any)(using Context) = x match
    case x: printing.Showable => x.show
    case _                    => String.valueOf(x)

  private def doTrace[T](question: => String, printer: Printers.Printer, showOp: T => String)(op: => T)(using Context): T =
    if ctx.mode.is(Mode.Printing) || !isForced && (printer eq Printers.noPrinter) then op
    else
      // Avoid evaluating question multiple time, since each evaluation
      // may cause some extra logging output.
      val q                   = question
      val leading             = s"==> $q?"
      def answer(res: String) = s"<== $q = $res"
      def trailing(res: T)    = answer(showOp(res))
      def margin = ctx.base.indentTab * ctx.base.indent
      def doLog(s: String) = if isForced then println(s) else report.log(s)(using logctx)
      var finalized = false
      def finalize(msg: String) = if !finalized then
        ctx.base.indent -= 1
        doLog(s"$margin$msg")
        finalized = true
      try
        doLog(s"$margin$leading")
        ctx.base.indent += 1
        val res = op
        finalize(trailing(res))
        res
      catch
        case ex: runtime.NonLocalReturnControl[T] => finalize(trailing(ex.value)); throw ex
        case ex: Throwable                        => finalize(answer(s"<missing> (with exception $ex)")); throw ex
end TraceSyntax
