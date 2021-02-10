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
    (declare-fun valueOf_Int (Int) Int)
    (declare-fun hasRole (Int String) Bool)
    (declare-const Unit Int)
    (assert (= Unit 0))
    ${DefineSortSMT("Field", "Int").toSMT("\n")}
    ; end static header
    """.trimIndent()

@Suppress("UNCHECKED_CAST")
fun generateSMT(ante : Formula, succ: Formula, modelCmd: String = "") : String {

    resetWildCards()

    val pre = deupdatify(ante)
    val post = deupdatify(Not(succ))

    val fields =  (pre.iterate { it is Field } + post.iterate { it is Field }) as Set<Field>
    setUsedHeaps(fields.map{libPrefix(it.dType)}.toSet())
    val vars =  ((pre.iterate { it is ProgVar} + post.iterate { it is ProgVar   }) as Set<ProgVar>).filter {!it.isFuture && it.name != "heap" && it.name !in specialHeapKeywords}
    val heaps =  ((pre.iterate { it is Function } + post.iterate{ it is Function }) as Set<Function>).filter { it.name.startsWith("NEW") }
    val futs =  ((pre.iterate { it is ProgVar  } + post.iterate { it is ProgVar }) as Set<ProgVar>).filter {it.isFuture }
    val funcs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("f_") }

    val preSMT = pre.toSMT()
    val postSMT = post.toSMT()

    val dTypesDecl = ADTRepos.toString()
    val functionDecl = FunctionRepos.toString()
    val wildcards: String = wildCardsConst.map { FunctionDeclSMT(it.key,it.value).toSMT("\n\t") }.joinToString("") { it }
    val fieldsDecl = fields.joinToString("\n\t"){ "(declare-const ${it.name} Field)"}
    val varsDecl = vars.joinToString("\n\t"){"(declare-const ${it.name} ${libPrefix(it.dType)})"}
    val objectsDecl = heaps.joinToString("\n\t"){"(declare-fun ${it.name} (${it.params.joinToString (" "){
        term ->
        if(term is DataTypeConst)
            term.dType
        else if(term is Function && term.name in booleanFunction)
            "Bool"
        else {
            "Int"
        }
    }}) Int)" }
    val futsDecl = futs.joinToString("\n") { "(declare-const ${it.name} Int)"}
    val funcsDecl = funcs.joinToString("\n") { "(declare-const ${it.name} Int)"}
    var fieldsConstraints = ""
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> if(libPrefix(f1.dType) == libPrefix(f2.dType)) fieldsConstraints += "(assert (not (= ${f1.name} ${f2.name})))" } } //??


    return """
;header
    $smtHeader
;data type declaration
    $dTypesDecl
;wildcards declaration
    $wildcards
;functions declaration
    $functionDecl
;fields declaration
    $fieldsDecl
;variables declaration
    $varsDecl
;objects declaration
    $objectsDecl
;futures declaration
    $futsDecl
;funcs declaration
    $funcsDecl
;fields constraints 
    $fieldsConstraints
    ; Precondition
    (assert $preSMT )
    ; Negated postcondition
    (assert $postSMT) 
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

private val wildCardsConst = mutableMapOf<String,String>()

private var countWildCard = 0

fun createWildCard(dType: String) : String{
    val wildCard = "_${countWildCard++}"
    wildCardsConst[wildCard] = dType
    return wildCard
}

fun refreshWildCard(name: String, dType: String) {
    wildCardsConst[name] = dType
}

fun resetWildCards() {
    wildCardsConst.clear()
    countWildCard = 0
}
