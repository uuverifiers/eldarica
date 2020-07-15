package lazabs.horn.concurrency

import org.apache.commons.lang3.SystemUtils

/**
  * @author Depeng Liang
  */
object Backend {

  // http://www.graphviz.org/cgi-bin/man?dot
  private val ENGINES = Set(
    "dot", "neato", "twopi", "circo", "fdp", "sfdp", "patchwork", "osage"
  )

  val ENGINGSEXECPATH: Map[String, String] = ENGINES.foldLeft(Map[String, String]())({
    (m, st) => {
      import sys.process._
      Map[String, String](st -> s"which $st".!!) ++ m
    }
  })

  // http://www.graphviz.org/doc/info/output.html
  private val FORMATS = Set(
    "bmp",
    "canon", "dot", "gv", "xdot", "xdot1.2", "xdot1.4",
    "cgimage",
    "cmap",
    "eps",
    "exr",
    "fig",
    "gd", "gd2",
    "gif",
    "gtk",
    "ico",
    "imap", "cmapx",
    "imap_np", "cmapx_np",
    "ismap",
    "jp2",
    "jpg", "jpeg", "jpe",
    "pct", "pict",
    "pdf",
    "pic",
    "plain", "plain-ext",
    "png",
    "pov",
    "ps",
    "ps2",
    "psd",
    "sgi",
    "svg", "svgz",
    "tga",
    "tif", "tiff",
    "tk",
    "vml", "vmlz",
    "vrml",
    "wbmp",
    "webp",
    "xlib",
    "x11"
  )

  /**
    * Return command for open a file for default
    */
  def viewFileCommand(): String = {
    if (SystemUtils.IS_OS_LINUX) {
      "xdg-open"
    }
    else if (SystemUtils.IS_OS_MAC || SystemUtils.IS_OS_MAC_OSX) {
      "open"
    }
    else throw new RuntimeException("only support mac OSX or Linux ")
  }

  /**
    * Return command for execution and name of the rendered file.
    *
    * @param engine   The layout commmand used for rendering ('dot', 'neato', ...).
    * @param format   The output format used for rendering ('pdf', 'png', ...).
    * @param filePath The output path of the source file.
    * @return render command to execute.
    */
  def command(engine: String, format: String, filePath: String = null): (String, String) = {
    require(ENGINES.contains(engine) == true, s"unknown engine: $engine")
    require(FORMATS.contains(format) == true, s"unknown format: $format")
    Option(filePath) match {
      case Some(path) => (s"${ENGINGSEXECPATH(engine)} -T$format -O $path", s"$path.$format")
      case None => (s"$engine -T$format", null)
    }
  }

  /**
    * Render file with Graphviz engine into format,  return result filename.
    *
    * @param engine   The layout commmand used for rendering ('dot', 'neato', ...).
    * @param format   The output format used for rendering ('pdf', 'png', ...).
    * @param filePath Path to the DOT source file to render.
    */
  @throws(classOf[RuntimeException])
  def render(engine: String = "dot", format: String = "pdf",
             filePath: String): String = {
    val (args, rendered) = command(engine, format, filePath)
    import sys.process._
    try {
      args !
    } catch {
      case _: Throwable =>
        val errorMsg =
          s"""failed to execute "$args", """ +
            """"make sure the Graphviz executables are on your systems' path"""
        throw new RuntimeException(errorMsg)
    }
    rendered
  }

  /**
    * Open filepath with its default viewing application (platform-specific).
    * For know only support linux.
    */
  @throws(classOf[RuntimeException])
  def view(filePath: String): Unit = {
    val command = s"$viewFileCommand $filePath"
    import sys.process._
    try {
      command !
    } catch {
      case _: Throwable =>
        val errorMsg = s"failed to execute $command"
        throw new RuntimeException(errorMsg)
    }
  }
}
