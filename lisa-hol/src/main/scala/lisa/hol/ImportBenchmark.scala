package lisa.hol

/** Run a bounded, fully checked HOL import without producing a heap dump. */
object ImportBenchmark:
  def main(args: Array[String]): Unit =
    require(args.length == 2 || args.length == 3, "Usage: ImportBenchmark <export-prefix> <theorem-count> [start-index]")
    val startAt = args.lift(2).fold(0)(_.toInt)
    Import.importFromPrefix(args(0), args(1).toInt, failFast = true, verifyEachStep = true, startAt = startAt)
