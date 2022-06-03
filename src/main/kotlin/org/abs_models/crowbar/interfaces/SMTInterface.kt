package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.main.ADTRepos.libPrefix
import org.abs_models.crowbar.main.ADTRepos.objects
import org.abs_models.crowbar.main.ADTRepos.setUsedHeaps
import org.abs_models.crowbar.types.booleanFunction
import org.abs_models.frontend.typechecker.DataTypeType
import java.io.File
import java.util.concurrent.TimeUnit


val valueOf = """
    (declare-fun   valueOf_ABS_StdLib_Int (ABS.StdLib.Fut) Int)
    (declare-fun   valueOf_ABS_StdLib_Bool(ABS.StdLib.Fut) Bool)
""".trimIndent()
val smtHeader = """
    ; static header
    (set-option :produce-models true)
    (set-logic ALL)
    (declare-fun valueOf_Int (Int) Int)
    (declare-fun hasRole (Int String) Bool)
    (define-sort ABS.StdLib.Int () Int)
    (define-sort ABS.StdLib.Float () Real)
    (define-sort ABS.StdLib.Bool () Bool)
    (define-sort ABS.StdLib.String () String)
    (declare-const Unit Int)
    (assert (= Unit 0))
    (declare-sort UNBOUND 0)
    ${DefineSortSMT("Field", "Int").toSMT("\n")}
    ; end static header
    """.trimIndent()

fun preGenerateSMT(ante: Formula, succ: Formula, modelCmd: String = "") : String{
    val pre = deupdatify(ante)

    val post = deupdatify(Not(succ))

    //output(generateSMT(pre, post, modelCmd))
    return generateSMT(pre, post, modelCmd)
}

@Suppress("UNCHECKED_CAST")
fun generateSMT(pre : LogicElement, post : LogicElement, modelCmd: String = "") : String {

    resetWildCards()

    //output("$succ.\n\n$post")
    val fields =  (pre.iterate { it is Field } + post.iterate { it is Field }) as Set<Field>

    setUsedHeaps(fields.map{libPrefix(it.concrType.qualifiedName)}.toSet())

    ((pre.iterate { it is DataTypeConst && isConcreteGeneric(it.concrType!!) } + post.iterate { it is DataTypeConst && isConcreteGeneric(it.concrType!!) }) as Set<DataTypeConst>).map {
        ADTRepos.addGeneric(it.concrType!! as DataTypeType) }

    val vars =  ((pre.iterate { it is ProgVar} + post.iterate { it is ProgVar   }) as Set<ProgVar>).filter {it.name != "heap" && it.name !in specialHeapKeywords}
    val heaps =  ((pre.iterate { it is Function } + post.iterate{ it is Function }) as Set<Function>).filter { it.name.startsWith("NEW") }
    val funcs =  ((pre.iterate { it is Function } + post.iterate { it is Function }) as Set<Function>).filter { it.name.startsWith("f_") }
    val fullAbs = (pre.iterate { it is FullAbstractTerm } + post.iterate { it is FullAbstractTerm }) as Set<FullAbstractTerm>
    val partAbs = (pre.iterate { it is PartialAbstractTerm } + post.iterate { it is PartialAbstractTerm }) as Set<PartialAbstractTerm>
    val concAbs = (pre.iterate {it is ConcreteOnAbstractTerm} + post.iterate {it is ConcreteOnAbstractTerm}) as Set<ConcreteOnAbstractTerm>
    val unknowns = (pre.iterate { it is UnknownTerm } + post.iterate { it is UnknownTerm }) as Set<UnknownTerm>
    val absExp = (pre.iterate { it is AbstractFormula } + post.iterate { it is AbstractFormula }) as Set<AbstractFormula>
    val preSMT = pre.toSMT()
    val postSMT = post.toSMT()

    //output("$concAbs")

    val functionDecl = FunctionRepos.toString()
    val primitiveTypesDecl = ADTRepos.primitiveDtypesDecl.filter{!it.type.isStringType}.joinToString("\n\t") { "(declare-sort ${it.qualifiedName} 0)" }
    val wildcards: String = wildCardsConst.map { FunctionDeclSMT(it.key,it.value).toSMT("\n\t") }.joinToString("") { it }
    val fieldsDecl = fields.joinToString("\n\t"){ "(declare-const ${it.name} Field)\n" +
            if(it.concrType.isInterfaceType)
                "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
            else ""}
    val varsDecl = vars.joinToString("\n\t"){"(declare-const ${it.name} ${
        if(it.concrType.isUnknownType)
            throw Exception("Var with unknown type: ${it.name}")
        else if (isConcreteGeneric(it.concrType) && !it.concrType.isFutureType) {
            ADTRepos.addGeneric(it.concrType as DataTypeType)
            genericTypeSMTName(it.concrType)
        }
        else
            libPrefix(it.concrType.qualifiedName)})\n" +
            if(it.concrType.isInterfaceType)
                "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
            else ""
    }

    val fullAbsDecl = (fullAbs.map{ "(declare-fun AEFull_${it.name.name} (Int Int ${
        it.accessibleValues.joinToString(" ") { term ->
            typeOfConcreteTermToSMT(term)
        }
    }) ${
        typeOfAbstractToSMT(it.concrType, it.name.name)
    })\n" }.toSet() +
            fullAbs.map {
                if (it.concrType.isInterfaceType)
                    "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                else ""
            }.toSet().filter { it != "" }).joinToString("\n\t") { it }

    //output("$fullAbs")
    //output("$partAbs")

    val partAbsDecl = (partAbs.map { "(declare-fun AEPartial_${it.name.name} (Int Int ${
        it.accessibleValues.joinToString(" ") { term ->
            typeOfConcreteTermToSMT(term)
        }
    } ${
        typeOfAbstractToSMT(it.concrType, it.name.name)
    }) ${
        typeOfAbstractToSMT(it.concrType, it.name.name)
    })\n" }.toSet() +
            partAbs.map {
                if (it.concrType.isInterfaceType)
                    "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                else ""
            }.toSet().filter { it != "" }).joinToString("\n\t") { it }

    val concAbsDecl = concAbs.map {
        "(declare-fun UC_${it.target.name} (${typeOfConcreteTermToSMT(it.value)} Int) Int)"
    }.toSet().joinToString ("\n\t"){ it }

    val unknownsDecl = unknowns.map {
        "(declare-const ${it.toSMT()} ${typeOfLocation(it.target)})"
    }.toSet().joinToString("\n\t") { it }

    val absExpDecl = absExp.joinToString("\n\t") { "(declare-const ${it.toSMT() } ${
        if(it.concrType.isUnknownType)
            throw Exception("Var with unknown type: ${it.name}")
        else if (isConcreteGeneric(it.concrType) && !it.concrType.isFutureType) {
            ADTRepos.addGeneric(it.concrType as DataTypeType)
            genericTypeSMTName(it.concrType)
        }
        else
            libPrefix(it.concrType.qualifiedName)})\n" +
    if(it.concrType.isInterfaceType)
        "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
    else ""}

    val objectImpl = heaps.joinToString("\n"){
        x:Function ->
        if(x.name in objects)
            objects[x.name]!!.types.joinToString("\n\t") {
                "(assert (implements " +
                        if(x.params.isNotEmpty()){
                        "(${x.name} " +
                        x.params.joinToString (" "){term -> term.toSMT()} +
                        ")  ${it.qualifiedName}))"}
                    else{
                        "${x.name} ${it.qualifiedName}))"
                        }

        }else ""

    }
    val objectsDecl = heaps.joinToString("\n\t"){"(declare-fun ${it.name} (${it.params.joinToString (" "){
        term ->
        if(term is DataTypeConst) {
            ADTRepos.addGeneric(term.concrType!! as DataTypeType)
            genericTypeSMTName(term.concrType)
        }
        else if(term is Function && term.name in booleanFunction) "Bool"
        else { "Int"
        }
    }}) Int)"

    }
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

;interface type declaration
    (declare-fun   implements (ABS.StdLib.Int Interface) Bool)
    (declare-fun   extends (Interface Interface) Bool)
    (assert (forall ((i1 Interface) (i2 Interface) (i3 Interface))
     (=> (and (extends i1 i2) (extends i2 i3))
      (extends i1 i3))))
      
    (assert (forall ((i1 Interface) (i2 Interface) (object ABS.StdLib.Int))
     (=> (and (extends i1 i2) (implements object i1))
      (implements object i2))))
      
      ${ADTRepos.interfaceExtendsToSMT()}
      
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
;abstract constants declaration
    $fullAbsDecl
    $partAbsDecl
    $concAbsDecl
;abstract expression declaration
    $absExpDecl
;unknowns constants declaration
    $unknownsDecl
;objects declaration
    $objectsDecl
    
;objects interface declaration
    $objectImpl
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
    output("$res")
    return res != null && res.trim() == "unsat"
}

fun evaluateSMT(ante: Formula, succ : Formula) : Boolean {
    val smtRep = preGenerateSMT(ante, succ)
    //output(smtRep)
    //output("ante : $ante \nsucc $succ\n$smtRep\n\n\n")
    if(verbosity >= Verbosity.VV) println("crowbar-v: \n$smtRep")
    return evaluateSMT(smtRep)
}

val wildCardsConst = mutableMapOf<String,String>()

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
