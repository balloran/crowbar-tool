package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.main.ADTRepos.libPrefix
import org.abs_models.crowbar.main.ADTRepos.setUsedHeaps
import org.abs_models.crowbar.types.booleanFunction
import java.io.File
import java.util.concurrent.TimeUnit

//(set-option :timeout ${timeoutS*1000})
val smtHeader = """
    ; static header
    (set-logic ALL)
    (declare-fun   valueOf (Int) Int)
    (declare-const Unit Int)
    (assert (= Unit 0))
    ${DefineSortSMT("Field", "Int").toSMT(true, "\n")}
    ; end static header
    """.trimIndent()

@Suppress("UNCHECKED_CAST")
fun generateSMT(ante : Formula, succ: Formula, modelCmd: String = "") : String {

    FunctionRepos.resetWildCards()

    var header = smtHeader
    val pre = deupdatify(ante)
    val post = deupdatify(Not(succ))

    val fields =  (pre.iterate { it is Field } + post.iterate { it is Field }) as Set<Field>
    setUsedHeaps(fields.map{libPrefix(it.dType)}.toSet())
    val vars =  ((pre.iterate { it is ProgVar } + post.iterate { it is ProgVar  }) as Set<ProgVar>).filter { it.name != "heap" && it.name !in specialHeapKeywords}
    val heaps =  ((pre.iterate { it is Function } + post.iterate{ it is Function }) as Set<Function>).filter { it.name.startsWith("NEW") }
    val futs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("fut_") }
    val funcs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("f_") }

    header += "\n" + ADTRepos
    header += FunctionRepos
    header = fields.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Field)"})
    header = vars.fold(header, {acc, nx-> acc+"\n(declare-const ${nx.name} ${libPrefix(nx.dType)})"})
    header = heaps.fold(header, {acc, nx-> "$acc\n(declare-fun ${nx.name} (${nx.params.joinToString (" "){
        if(it is DataTypeConst)
            it.dType
        else if(it is Function && it.name in booleanFunction)
            "Bool"
        else {
            "Int"
        }
    }}) Int)" })
    header = futs.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Int)"})
    header = funcs.fold(header, { acc, nx-> acc +"\n(declare-const ${nx.name} Int)"})
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> if(libPrefix(f1.dType) == libPrefix(f2.dType)) header += "\n (assert (not (= ${f1.name} ${f2.name})))" } } //??

    return """
    $header 
    ; Precondition
    (assert ${pre.toSMT()} )
    ; Negated postcondition
    (assert ${post.toSMT()}) 
    (check-sat)
    $modelCmd
    (exit)
    """.trimIndent()
}

/* https://stackoverflow.com/questions/35421699 */
fun String.runCommand(
        workingDir: File = File("."),
        timeoutAmount: Long = 60,
        timeoutUnit: TimeUnit = TimeUnit.SECONDS
): String? = try {
    ProcessBuilder(split("\\s".toRegex()))
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start().apply { waitFor(timeoutAmount, timeoutUnit) }
            .inputStream.bufferedReader().readText()
} catch (e: java.io.IOException) {
    e.printStackTrace()
    null
}

fun plainSMTCommand(smtRep: String) : String? {
    val path = "${tmpPath}out.smt2"
    File(path).writeText(smtRep)
    return "$smtPath $path".runCommand()
}

fun evaluateSMT(smtRep : String) : Boolean {
    val res = plainSMTCommand(smtRep)
    return res != null && res.trim() == "unsat"
}

fun evaluateSMT(ante: Formula, succ: Formula) : Boolean {
    val smtRep = generateSMT(ante, succ)
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$smtRep")
    return evaluateSMT(smtRep)
}
