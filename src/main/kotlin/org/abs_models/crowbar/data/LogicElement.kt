package org.abs_models.crowbar.data

import org.abs_models.crowbar.interfaces.createWildCard
import org.abs_models.crowbar.interfaces.refreshWildCard
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.frontend.ast.DataTypeDecl
import org.abs_models.frontend.typechecker.Type

interface ProofElement: Anything {
    fun toSMT(indent:String="") : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
}

interface LogicElement: Anything {
    fun toSMT(indent:String="") : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
}
interface Formula: LogicElement
interface Term : LogicElement
//interface LogicVariable : Term //for FO

val binaries = listOf(">=","<=","<",">","=","!=","+","-","*","/","&&","||")

data class HeapDecl(val dtype: String) : ProofElement{

    fun name(str: String) = "${str}_${(if(dtype == "Int"){"Int"}else{dtype}).replace(".", "_")}"
    val anon :String = name("anon")
    val old :String  = name("old")
    val last :String = name("last")
    val heap :String = name("heap")
    val heapType :String = name("Heap")
    val field :String = "Field"

    override fun toSMT(indent:String): String {

        var ret = "\n; $dtype Heap declaration"
        ret += DefineSortSMT(heapType, "(Array $field ${ADTRepos.libPrefix(dtype)})").toSMT("\n")//todo: refactor hard-code
        ret += DeclareConstSMT(heap, heapType).toSMT("\n")
        ret += DeclareConstSMT(old, heapType).toSMT("\n")
        ret += DeclareConstSMT(last, heapType).toSMT("\n")
        ret += FunctionDeclSMT(anon, heapType, listOf(heapType)).toSMT("\n")
        return ret
    }
}

data class DataTypesDecl(val dTypesDecl : List<DataTypeDecl>) : ProofElement{
    override fun toSMT(indent:String): String {
        var valueOfs = ""
        if(dTypesDecl.isNotEmpty()) {
            val dTypeDecl = mutableListOf<ArgsSMT>()
            val dTypeValsDecl = mutableListOf<Term>()
            for (dType in dTypesDecl) {
                valueOfs += "(declare-fun   valueOf_${dType.qualifiedName.replace(".","_")} (Int) ${dType.qualifiedName})\n"
                dTypeDecl.add(ArgsSMT(dType.qualifiedName, listOf(Function("0"))))
                val dTypeValDecl = mutableListOf<Term>()
                for (dataConstructor in dType.dataConstructorList) {
                    var count = 0
                    dTypeValDecl.add(
                        ArgsSMT(dataConstructor.qualifiedName,
                            dataConstructor.constructorArgList.map {
                                ArgsSMT(
                                    "${dataConstructor.qualifiedName}_${count++}",
                                    listOf(Function(ADTRepos.libPrefix(it.type.qualifiedName)))
                                )
                            })
                    )
                }
                dTypeValsDecl.add(ArgSMT(dTypeValDecl))
            }

            val decl = Function(
                "declare-datatypes", (
                        listOf(
                            ArgSMT(dTypeDecl),
                            ArgSMT(dTypeValsDecl)
                        ))
            )

            return "; DataTypes declaration\n${decl.toSMT()}\n$valueOfs"
        }
        return ""
    }
}

//data class Something(val dtype: String) :Term{
//    override fun toSMT(isInForm : Boolean, indent:String) : String {
//        return "Something_${dtype.replace(".", "_")}"
//    }
//}

data class ArgsSMT(val name : String, val params : List<Term> = emptyList()) : Term{
    override fun toSMT(indent:String) : String {
        if(params.isEmpty())
            return "($name)"

        val list = params.joinToString (" "){it.toSMT()}
        return "($name $list)"
    }
}
data class ArgSMT(val params : List<Term> = emptyList()) : Term{
    override fun toSMT(indent:String): String {
        val list = params.joinToString (" "){it.toSMT()}
        return "\n\t($list)"
    }
}

data class FunctionDeclSMT(val name : String, val type: String, val params :List<String> = listOf()) :ProofElement{
    override fun toSMT(indent:String): String {
        return "$indent(declare-fun $name (${params.joinToString(" ") {it}}) $type)"
    }
}


data class DefineSortSMT(val name :String, val type: String, val params :List<String> = listOf()):ProofElement{
    override fun toSMT(indent:String): String {
        return "$indent(define-sort $name (${params.joinToString(" ") {it}}) $type)"
    }
}

data class DeclareConstSMT(val name :String, val type: String):ProofElement{
    override fun toSMT(indent:String): String {
        return "$indent(declare-const $name $type)"
    }
}

//data class Assert(val formula: Formula) : ProofElement{
//    override fun toSMT(isInForm: Boolean): String {
//        return "(assert ${formula.toSMT(isInForm)})"
//    }
//}
//
//data class Distinct(val params :List<Term>) :Formula {
//    override fun toSMT(isInForm : Boolean) : String {
//        return "(distinct ${params.joinToString(" "){it.toSMT(isInForm)}})"
//    }
//}
//
//data class Forall(val params :List<Pair<Term,Term>>, val formula: Formula) :Formula{
//    override fun toSMT(isInForm : Boolean) : String {
//        if(params.isEmpty())
//            return formula.toSMT(isInForm)
//        return "(forall (${params.map { pair -> "${pair.first.toSMT(isInForm)} ${pair.second.toSMT(isInForm)}" }.joinToString(" ") { "($it)" }}) ${formula.toSMT(isInForm)})"
//    }
//}

data class FormulaAbstractVar(val name : String) : Formula, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
    override fun toSMT(indent:String) : String = name
}

// Crowbar uses type-agnostic heaps internally that can store any data type
// For SMT translation, we have to use separate heaps for different types
// Therefore, we have to translate the generic heap expressions to properly
// typed ones
fun filterHeapTypes(term : Term, dtype: String) : String{
    val smtdType = ADTRepos.getSMTDType(dtype)
    if (term is Function ) {
        // Remove stores that do not change the sub-heap for type dType
        return if(term.name == "store") {
            if (ADTRepos.libPrefix((term.params[1] as Field).dType) == dtype)
                "(store " +
                        "${filterHeapTypes(term.params[0], dtype)} " +
                        "${term.params[1].toSMT()} " +
                        "${term.params[2].toSMT()})"
            else
                filterHeapTypes(term.params[0], dtype)
            // Rewrite generic anon to correctly typed anon function
        } else if (term.name == "anon")
            "(${smtdType.anon} ${filterHeapTypes(term.params[0], dtype)})"
        else
            throw Exception("${term.prettyPrint()}  is neither an heap nor anon or store function")

    }
    // Rewrite generic heap variables to correctly typed sub-heap variables
    else if(term is ProgVar && term.dType == "Heap"){
        return when (term) {
            is OldHeap -> smtdType.old
            is LastHeap -> smtdType.last
            is Heap -> smtdType.heap
            else -> term.name
        }
    }
    else
        throw Exception("${term.prettyPrint()}  is neither an heap nor anon or store function")

}

data class Function(val name : String, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

    override fun toSMT(indent:String): String {

        if(name == "valueOf") {
            if(params[0] is ProgVar)
                return "(valueOf_${
                    ADTRepos.libPrefix((params[0] as ProgVar).dType).replace(".", "_")} ${(params[0] as ProgVar).name})"
            else
                throw Exception("parameter of \"valueOf\" expects Progvar or Future, actual value: ${params[0]}")
        }
        if(name == "select") {
            val heapType = ADTRepos.libPrefix((params[1] as Field).dType)
            val fieldName = params[1].toSMT()
            return "(select ${filterHeapTypes(params[0], heapType)} $fieldName)"
        }

        if(params.isEmpty()) {
            if(name.startsWith("-")) return "(- ${name.substring(1)})" //CVC4 requires -1 to be passed as (- 1)
            return name
        }
        val list = params.fold("",{acc,nx -> acc + " ${nx.toSMT()}"})
        return getSMT(name, list)
    }
}

data class DataTypeConst(val name : String, val dType : String, val concrType: Type?, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        return name + ":" + dType+"("+params.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

    override fun toSMT(indent:String): String {
        val back = name
        if(params.isEmpty())
            return name
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toSMT()}"})
        return "($back $list)"
    }

}

fun extractPatternMatching(match: Term, branchTerm: DataTypeConst, freeVars: Set<String>): Formula {
    var countParameter = 0

    return branchTerm.params.foldRight(Is(branchTerm.name, match)) { nx, acc: Formula ->
        val parameter = Function("${branchTerm.name}_${countParameter++}", listOf(match))
        And(
            acc,
            if (nx is DataTypeConst) {
                extractPatternMatching(
                    parameter,
                    nx,
                    freeVars
                )
            } else if (nx is ProgVar && nx.name in freeVars)
                Eq(parameter, nx)
            else
                True
        )
    }
}

data class Case(val match : Term, val expectedType :String, val branches : List<BranchTerm>, val freeVars : Set<String>) : Term {
    private lateinit var wildCardName: String

    override fun toSMT(indent:String): String {
        if (branches.isNotEmpty() ){
            if(!::wildCardName.isInitialized)
                wildCardName = createWildCard(expectedType)
            else
                refreshWildCard(wildCardName, expectedType)
                
            val firstMatchTerm = Function(wildCardName)

            val branchTerm = branches.foldRight(firstMatchTerm as Term, { branchTerm: BranchTerm,acc: Term ->
                var indexOfParam = -1
                val matchSMT =
                    if(branchTerm.matchTerm is DataTypeConst)
                        extractPatternMatching(match, branchTerm.matchTerm,freeVars)
                    else if(branchTerm.matchTerm is ProgVar && branchTerm.matchTerm.name in freeVars )
                        Eq(match, branchTerm.matchTerm)
                    else
                        True
                if(branchTerm.matchTerm is DataTypeConst) {
                    indexOfParam = branchTerm.matchTerm.params.indexOf(branchTerm.branch)
                }
                val branch =
                if (branchTerm.matchTerm is DataTypeConst && indexOfParam != -1 )
                    Function("${branchTerm.matchTerm.name}_$indexOfParam", listOf(match))
                else
                    branchTerm.branch
                Ite(matchSMT, branch, acc)
            })
            return branchTerm.toSMT()

        }else
            throw Exception("No branches")
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + match.iterate(f) + branches.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})
}

data class BranchTerm(val matchTerm : Term, val branch : Term) :Term {
    override fun toSMT(indent:String): String {
        return "$indent(${matchTerm.toSMT()} ${branch.toSMT()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + matchTerm.iterate(f) + branch.iterate(f)

}
data class UpdateOnTerm(val update : UpdateElement, val target : Term) : Term {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to Z3")
}
data class Impl(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        return "(${left.prettyPrint()}) -> (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(indent:String) : String = "(=> ${left.toSMT()} ${right.toSMT()})"
}
data class And(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == True) return right.prettyPrint()
        if(right == True) return left.prettyPrint()
        return "(${left.prettyPrint()}) /\\ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(indent:String) : String = "(and ${left.toSMT()} ${right.toSMT()})"
}
data class Or(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == False) return right.prettyPrint()
        if(right == False) return left.prettyPrint()
        return "(${left.prettyPrint()}) \\/ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(indent:String) : String = "(or ${left.toSMT()} ${right.toSMT()})"
}
data class Not(val left : Formula) : Formula {
    override fun prettyPrint(): String {
        return "!"+left.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f)
    override fun toSMT(indent:String) : String = "(not ${left.toSMT()})"
}
data class Predicate(val name : String, val params : List<Term> = emptyList()) : Formula {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})
    override fun toSMT(indent:String) : String {
        if(params.isEmpty()) return name
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toSMT()}"})
        return getSMT(name, list)
    }
}
data class UpdateOnFormula(val update : UpdateElement, val target : Formula) : Formula {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to Z3")
}

data class Ite(val condition :Formula, val term1 : Term, val term2 : Term) : Term{
    override fun toSMT(indent:String): String {
        return "(ite ${condition.toSMT()}" +
                "\n\t\t$indent${term1.toSMT("$indent\t")}" +
                "\n\t\t$indent${term2.toSMT("$indent\t")})"
    }
}

data class Is(val typeName : String, val term : Term) :Formula{
    override fun toSMT(indent:String): String {
        return "((_ is $typeName) ${term.toSMT()})"
    }
}

data class Exists(val params :List<ProgVar>, val formula: Formula) : Formula{
    override fun toSMT(indent:String): String {
        return "(exists (${params.joinToString(" ") { "(${it.name} ${ADTRepos.libPrefix(it.dType)})" }}) ${formula.toSMT()})"
    }
}

data class Eq(val term1: Term, val term2 : Term) : Formula{
    override fun toSMT(indent:String): String {
        return "(= ${term1.toSMT()} ${term2.toSMT()})"
    }
}

object True : Formula {
    override fun prettyPrint(): String {
        return "true"
    }
    override fun toSMT(indent:String) : String = "true"
}
object False : Formula {
    override fun prettyPrint(): String {
        return "false"
    }
    override fun toSMT(indent:String) : String = "false"
}

val specialHeapKeywords = mapOf(OldHeap.name to OldHeap, LastHeap.name to LastHeap)

data class HeapType(val name: String) : Type() {
    override fun copy(): Type {
        return this
    }
    override fun getSimpleName(): String {
        return name
    }

}


object Heap : ProgVar("heap", "Heap", HeapType("Heap"))
object OldHeap : ProgVar("old", "Heap", HeapType("Heap"))
object LastHeap : ProgVar("last", "Heap", HeapType("Heap"))

fun store(field: Field, value : Term) : Function = Function("store", listOf(Heap, field, value))
fun select(field : Field, heap: ProgVar = Heap) : Function = Function("select", listOf(heap, field))
fun anon(heap : Term) : Function = Function("anon", listOf(heap))
fun poll(term : Term) : Function = Function("poll", listOf(term))
fun readFut(term : Expr) : Expr = SExpr("valueOf", listOf(term))
fun exprToTerm(input : Expr, specialKeyword : String="NONE") : Term {//todo: add check for non-field reference inside old and last
    return when(input){
        is ProgVar -> input
        is Field -> {
            if(specialKeyword != "NONE" && specialHeapKeywords.containsKey(specialKeyword))
                select(input, specialHeapKeywords[specialKeyword] as ProgVar)
            else if(specialKeyword != "NONE")
                throw Exception("The special heap keyword $specialKeyword is not supported")
            else
                select(input)
        }
        is PollExpr -> poll(exprToTerm(input.e1))
        is Const -> Function(input.name)
        is SExpr -> {
            if (specialHeapKeywords.containsKey(input.op)) {
                if (input.e.size == 1)
                    exprToTerm(input.e[0], input.op)
                else
                    throw Exception("Special keyword ${input.op} must have one argument, actual arguments size:" + input.e.size)
            }
            else
                Function(input.op, input.e.map { ex -> exprToTerm(ex, specialKeyword) })
        }
        is DataTypeExpr -> {
            DataTypeConst(input.name, input.dType, input.concrType, input.e.map { ex -> exprToTerm(ex, specialKeyword) })
        }
        is CaseExpr -> {
            val match =exprToTerm(input.match)
            Case(match, input.expectedType, input.content.map { ex -> BranchTerm(exprToTerm(ex.matchTerm, specialKeyword), exprToTerm(ex.branch, specialKeyword)) },input.freeVars)
        }
        else -> throw Exception("Expression cannot be converted to term: ${input.prettyPrint()} (${input.javaClass})")
    }
}

fun exprToForm(input : Expr, specialKeyword : String="NONE") : Formula {//todo: add check for non-field reference inside old and last
    if(input is SExpr && input.op == "&&" && input.e.size ==2 ) return And(exprToForm(input.e[0], specialKeyword), exprToForm(input.e[1], specialKeyword))
    if(input is SExpr && input.op == "||" && input.e.size ==2 ) return Or(exprToForm(input.e[0], specialKeyword), exprToForm(input.e[1], specialKeyword))
    if(input is SExpr && input.op == "->" && input.e.size ==2 ) return Impl(exprToForm(input.e[0], specialKeyword), exprToForm(input.e[1], specialKeyword))
    if(input is SExpr && input.op == "!" && input.e.size ==1 ) return Not(exprToForm(input.e[0]))
    if(input is SExpr && input.op == "!=") return Not(exprToForm(SExpr("=",input.e), specialKeyword))

    if(input is SExpr){
        if (specialHeapKeywords.containsKey(input.op)){//todo: fix for last
            if(input.e.size == 1) {
                return exprToForm(input.e[0], input.op)
            } else
                throw Exception("Special keywords must have one argument, actual arguments size:" + input.e.size)
        }
        return Predicate(input.op, input.e.map { ex -> exprToTerm(ex, specialKeyword) })
    }
    if(input is Field || input is ProgVar || input is Const)
        return exprToForm(SExpr("=",listOf(input, Const("true"))), specialKeyword) //todo: remove useless comparison with true
    throw Exception("Expression cannot be converted to formula: $input")
}

fun deupdatify(input: LogicElement) : LogicElement {
    return when(input){
        is UpdateOnTerm -> deupdatify(apply(input.update, input.target))
        is UpdateOnFormula -> deupdatify(apply(input.update, input.target))
        is Function -> Function(input.name, input.params.map { p -> deupdatify(p) as Term })
        is Predicate -> Predicate(input.name, input.params.map { p -> deupdatify(p) as Term })
        is Impl -> Impl(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is And -> And(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is Or -> Or(deupdatify(input.left) as Formula, deupdatify(input.right) as Formula)
        is Not -> Not(deupdatify(input.left) as Formula)
        else -> input
    }
}

fun apply(update: UpdateElement, input: LogicElement) : LogicElement {
    return when(update) {
        is EmptyUpdate -> input
        is ElementaryUpdate -> subst(input, update.lhs, update.rhs)
        is ChainUpdate -> apply(update.left, apply(update.right, input))
        else -> input
    }
}


fun subst(input: LogicElement, map: Map<LogicElement,LogicElement>) : LogicElement {
    if(map.containsKey(input)) return map.getValue(input)
    when(input){
        is EmptyUpdate -> return EmptyUpdate
        is ElementaryUpdate -> return ElementaryUpdate(input.lhs, subst(input.rhs, map) as Term)
        is ChainUpdate -> {
            if(map.keys.any { it is ProgVar && input.left.assigns(it)}) return ChainUpdate(subst(input.left, map) as UpdateElement, input.right)
            return ChainUpdate(subst(input.left, map) as UpdateElement, subst(input.right, map) as UpdateElement)
        }
//        is DataTypeConst -> return Function(input.name, input.params.map { p -> subst(p, map) as Term })
        is DataTypeConst -> return DataTypeConst(input.name, input.dType, input.concrType, input.params.map { p -> subst(p, map) as Term })
//        is Case -> return Case(subst(input.match, map) as Term, input.expectedType, input.branches.map { p -> subst(p, map) as BranchTerm }, input.freeVars)
        is Function -> return Function(input.name, input.params.map { p -> subst(p, map) as Term })
        is Predicate -> return Predicate(input.name, input.params.map { p -> subst(p, map) as Term })
        is Impl -> return Impl(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is And -> return And(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is Or -> return Or(subst(input.left, map) as Formula, subst(input.right, map) as Formula)
        is Not -> return Not(subst(input.left,map) as Formula)
        is UpdateOnTerm -> {
            if(map.keys.any { it is ProgVar && input.update.assigns(it)}) return UpdateOnTerm(subst(input.update, map) as UpdateElement, input.target)
            return UpdateOnTerm(subst(input.update, map) as UpdateElement, subst(input.target, map) as Term)
        }
        is UpdateOnFormula -> {
            if(map.keys.any { it is ProgVar && input.update.assigns(it)}) return UpdateOnFormula(subst(input.update, map) as UpdateElement, input.target)
            return UpdateOnFormula(subst(input.update, map) as UpdateElement, subst(input.target, map) as Formula)
        }
        else                -> return input
    }
}
fun subst(input: LogicElement, elem : ProgVar, term : Term) : LogicElement = subst(input, mapOf(Pair(elem,term)))


fun valueOfFunc(t : Term) = Function("valueOf", listOf(t))

fun getSMT(name: String, params: String): String{
    val ret =
        when(name) {
            "!=" -> "not ${getSMT("=", params)}"
            "||" -> "or $params"
            "&&" -> "and $params"
            "!" -> "not $params"
            else -> "$name $params"
        }
    return "($ret)"
}

fun prettyPrintFunction(params: List<Term>, name: String):String{
    if(params.isEmpty()) return name
    if(binaries.contains(name) && params.size == 2) return params[0].prettyPrint() + name + params[1].prettyPrint()
    return name+"("+params.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
}
/*
fun subst(input: LogicElement, elem : ProgVar, term : Term) : LogicElement {
    when(input){
        elem                -> return term
        is EmptyUpdate -> return EmptyUpdate
        is ElementaryUpdate -> return ElementaryUpdate(input.lhs, subst(input.rhs, elem, term) as Term)
        is ChainUpdate -> {
            if(input.left.assigns(elem)) return ChainUpdate(subst(input.left, elem, term) as UpdateElement, input.right)
            return ChainUpdate(subst(input.left, elem, term) as UpdateElement, subst(input.right, elem, term) as UpdateElement)
        }
        is Function -> return Function(input.name, input.params.map { p -> subst(p, elem, term) as Term })
        is Predicate -> return Predicate(input.name, input.params.map { p -> subst(p, elem, term) as Term })
        is Impl -> return Impl(subst(input.left, elem, term) as Formula, subst(input.right, elem, term) as Formula)
        is And -> return And(subst(input.left, elem, term) as Formula, subst(input.right, elem, term) as Formula)
        is Or -> return Or(subst(input.left, elem, term) as Formula, subst(input.right, elem, term) as Formula)
        is Not -> return Not(subst(input.left, elem, term) as Formula)
        is UpdateOnTerm -> {
            if(input.update.assigns(elem)) return UpdateOnTerm(subst(input.update, elem, term) as UpdateElement, input.target)
            return UpdateOnTerm(subst(input.update, elem, term) as UpdateElement, subst(input.target, elem, term) as Term)
        }
        is UpdateOnFormula -> {
            if(input.update.assigns(elem)) return UpdateOnFormula(subst(input.update, elem, term) as UpdateElement, input.target)
            return UpdateOnFormula(subst(input.update, elem, term) as UpdateElement, subst(input.target, elem, term) as Formula)
        }
        else                -> return input
    }
}
 */