val Regexp = """\{\{([^{}]+)\}\}""".r

val map = Map("VARIABLE1" -> "VALUE1", "VARIABLE2" -> "VALUE2", "VARIABLE3" -> "VALUE3")

val incomingData = "I'm {{VARIABLE1}}. I'm {{VARIABLE2}}. And I'm {{VARIABLE3}}. And also {{VARIABLE1}}"


def replace(incoming: String) = {
  def replace(what: String, `with`: String)(where: String) = where.replace(what, `with`)

  val composedReplace = Regexp.findAllMatchIn(incoming).map { m => replace(m.matched, map(m.group(1)))(_) }.reduceLeftOption((lf, rf) => lf compose rf).getOrElse(identity[String](_))
  composedReplace(incomingData)
}

println(replace(incomingData))

//OUTPUT: I'm VALUE1. I'm VALUE2. And I'm VALUE3. And also VALUE1