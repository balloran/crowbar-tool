package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.main.ADTRepos.libPrefix
import org.abs_models.crowbar.main.ADTRepos.setUsedHeaps
import org.abs_models.crowbar.types.booleanFunction
import org.abs_models.frontend.typechecker.DataTypeType
import java.io.File
import java.util.concurrent.TimeUnit

//(set-option :timeout ${timeoutS*1000})

val valueOf = """
    (declare-fun   valueOf_ABS_StdLib_Int (ABS.StdLib.Fut) Int)
    (declare-fun   valueOf_ABS_StdLib_Bool(ABS.StdLib.Fut) Bool)
""".trimIndent()
val smtHeader = """
    ; static header
    (set-logic ALL)
    (declare-fun valueOf_Int (Int) Int)
    (declare-fun hasRole (Int String) Bool)
    (define-sort ABS.StdLib.Int () Int)
    (define-sort ABS.StdLib.Bool () Bool)
    (declare-const Unit Int)
    (assert (= Unit 0))
    (declare-sort UNBOUND 0)
    ${DefineSortSMT("Field", "Int").toSMT("\n")}
    ; end static header
    """.trimIndent()

@Suppress("UNCHECKED_CAST")
fun generateSMT(ante : Formula, succ: Formula, modelCmd: String = "") : String {

    resetWildCards()
    val pre = deupdatify(ante)

    val post = deupdatify(Not(succ))
    val fields =  (pre.iterate { it is Field } + post.iterate { it is Field }) as Set<Field>

    //todo finish implementation: missing binding of the contract of functions with generics
//    val genericFunctionsDecl = ((pre.iterate { it is Function && it.name in FunctionRepos.genericFunctions} + post.iterate { it is Function && it.name in FunctionRepos.genericFunctions}) as Set<Function>).map {
//        println("${it.name}::function " + FunctionRepos.genericFunctions[it.name])
//        val genericType = FunctionRepos.genericFunctions[it.name]!!.first
//        val genericParams = FunctionRepos.genericFunctions[it.name]!!.second
//        val contract = FunctionRepos.genericFunctions[it.name]!!.third
//        val concreteParams = it.params.map { param -> getReturnType(param) }
//
//        val mapGenericConcrete = genericParams.zip(concreteParams).filter { pair -> pair.first != pair.second }.toMap()
//        val concreteTypes = genericType.typeArgs.map { gT :Type -> if(gT in mapGenericConcrete) mapGenericConcrete[gT] else gT }
//        val additionalName = concreteTypes.joinToString("_") { cT -> genericTypeSMTName(cT!!) }
//
//        val zippedParams = contract.params.zip(concreteParams)
//
//
//        val paramsTyped = zippedParams.joinToString(" ") { zipped -> "(${(zipped.first as Function).name} ${zipped.second.qualifiedName})" }
//
//
//        "(declare-fun ${it.name}_$additionalName (${concreteParams.joinToString(" "){ cT -> genericTypeSMTName(cT) }} ) ${
//            genericTypeSMTName(genericType)}_$additionalName)" +
//                "\n(assert (forall ($paramsTyped) ${contract.name.replace(it.name, "${it.name}_$additionalName")}))"
//
//    }.joinToString("\n")

    setUsedHeaps(fields.map{libPrefix(it.concrType.qualifiedName)}.toSet())

    ((pre.iterate { it is DataTypeConst && isConcreteGeneric(it.concrType!!) } + post.iterate { it is DataTypeConst && isConcreteGeneric(it.concrType!!) }) as Set<DataTypeConst>).map {
        ADTRepos.addGeneric(it.concrType!! as DataTypeType) }



    val vars =  ((pre.iterate { it is ProgVar} + post.iterate { it is ProgVar   }) as Set<ProgVar>).filter {it.name != "heap" && it.name !in specialHeapKeywords}
    val heaps =  ((pre.iterate { it is Function } + post.iterate{ it is Function }) as Set<Function>).filter { it.name.startsWith("NEW") }
    val funcs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("f_") }
    val preSMT = pre.toSMT()
    val postSMT = post.toSMT()

    val functionDecl = FunctionRepos.toString()
    val primitiveTypesDecl = ADTRepos.primitiveDtypesDecl.joinToString("\n\t") { "(declare-sort ${it.qualifiedName} 0)" }
    val wildcards: String = wildCardsConst.map { FunctionDeclSMT(it.key,it.value).toSMT("\n\t") }.joinToString("") { it }
    val fieldsDecl = fields.joinToString("\n\t"){ "(declare-const ${it.name} Field)"}
    val varsDecl = vars.joinToString("\n\t"){"(declare-const ${it.name} ${
        if(it.concrType.isUnknownType)
            throw Exception("Var with unknown type: ${it.name}")
        else if (isConcreteGeneric(it.concrType) && !it.concrType.isFutureType) {
            ADTRepos.addGeneric(it.concrType as DataTypeType)
            genericTypeSMTName(it.concrType)
        }
        else
            libPrefix(it.concrType.qualifiedName)})"} //todo: fix this, it is needed from Basic Test
    val objectsDecl = heaps.joinToString("\n\t"){"(declare-fun ${it.name} (${it.params.joinToString (" "){
        term ->
        if(term is DataTypeConst) {
            ADTRepos.addGeneric(term.concrType!! as DataTypeType)
            genericTypeSMTName(term.concrType)
        }
        else if(term is Function && term.name in booleanFunction)
            "Bool"
        else {
            "Int"
        }
    }}) Int)" }
    val funcsDecl = funcs.joinToString("\n") { "(declare-const ${it.name} Int)"}
    var fieldsConstraints = ""
    fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> if(libPrefix(f1.concrType.qualifiedName) == libPrefix(f2.concrType.qualifiedName)) fieldsConstraints += "(assert (not ${Eq(f1,f2).toSMT()}))" } } //??


    return """
;header
    $smtHeader
;primitive type declaration
    $primitiveTypesDecl
;valueOf
    $valueOf
;data type declaration
    ${ADTRepos.dTypesToSMT()}
;generics declaration
    ${ADTRepos.genericsToSMT()}
;heaps declaration
    ${ADTRepos.heapsToSMT()}
;wildcards declaration
    $wildcards
;functions declaration
    $functionDecl
;generic functions declaration :to be implemented and added
;    
;fields declaration
    $fieldsDecl
;variables declaration
    $varsDecl
;objects declaration
    $objectsDecl
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
