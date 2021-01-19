package org.abs_models.crowbar.data

import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.frontend.ast.DataTypeDecl

interface ProofElement: Anything {
    fun toSMT(isInForm : Boolean, indent:String="") : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
}

interface LogicElement: Anything {
    fun toSMT(isInForm : Boolean, indent:String="") : String //isInForm is set when a predicate is expected, this is required for the interpretation of Bool Terms as Int Terms
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

    override fun toSMT(isInForm: Boolean, indent:String): String {

        var ret = "\n; $dtype Heap declaration"
        ret += DefineSortSMT(heapType, "(Array $field ${ADTRepos.libPrefix(dtype)})").toSMT(isInForm, "\n")//todo: refactor hard-code
        ret += DeclareConstSMT(heap, heapType).toSMT(isInForm, "\n")
        ret += DeclareConstSMT(old, heapType).toSMT(isInForm, "\n")
        ret += DeclareConstSMT(last, heapType).toSMT(isInForm, "\n")
        ret += FunctionDeclSMT(anon, heapType, listOf(heapType)).toSMT(isInForm,"\n")
        return ret
    }
}

data class DataTypesDecl(val dTypesDecl : List<DataTypeDecl>) : ProofElement{
    override fun toSMT(isInForm: Boolean, indent:String): String {
        if(dTypesDecl.isNotEmpty()) {
            val dTypeDecl = mutableListOf<ArgsSMT>()
            val dTypeValsDecl = mutableListOf<Term>()
            for (dType in dTypesDecl) {
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

            return "; DataTypes declaration\n" + decl.toSMT(isInForm)
        }
        return ""
    }
}

data class Something(val dtype: String) :Term{
    override fun toSMT(isInForm : Boolean, indent:String) : String {
        return "Something_${dtype.replace(".", "_")}"
    }
}

data class ArgsSMT(val name : String, val params : List<Term> = emptyList()) : Term{
    override fun toSMT(isInForm : Boolean, indent:String) : String {
        if(params.isEmpty())
            return "($name)"

        val list = params.joinToString (" "){it.toSMT(isInForm)}
        return "($name $list)"
    }
}
data class ArgSMT(val params : List<Term> = emptyList()) : Term{
    override fun toSMT(isInForm : Boolean, indent:String) : String {
        val list = params.joinToString (" "){it.toSMT(isInForm)}
        return "\n\t($list)"
    }
}

data class FunctionDeclSMT(val name : String, val type: String, val params :List<String> = listOf()) :ProofElement{
    override fun toSMT(isInForm: Boolean, indent:String): String {
        return "$indent(declare-fun $name (${params.joinToString(" ") {it}}) $type)"
    }
}


data class DefineSortSMT(val name :String, val type: String, val params :List<String> = listOf()):ProofElement{
    override fun toSMT(isInForm: Boolean, indent:String): String {
        return "$indent(define-sort $name (${params.joinToString(" ") {it}}) $type)"
    }
}

data class DeclareConstSMT(val name :String, val type: String):ProofElement{
    override fun toSMT(isInForm: Boolean, indent:String): String {
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
    override fun toSMT(isInForm : Boolean, indent:String) : String = name
}

// Crowbar uses type-agnostic heaps internally that can store any data type
// For SMT translation, we have to use separate heaps for different types
// Therefore, we have to translate the generic heap expressions to properly
// typed ones
fun filterHeapTypes(term : Term, dtype: String) : String{
    val smtdType = ADTRepos.getSMTDType(dtype)
    if (term is Function ) {
        // Remove stores that do not change the sub-heap for type dType
        if(term.name == "store") {
            if (ADTRepos.libPrefix((term.params[1] as Field).dType) == dtype)
                return "(store " +
                        "${filterHeapTypes(term.params[0], dtype)} " +
                        "${term.params[1].toSMT(false)} " +
                        "${term.params[2].toSMT(false)})"
            else
                return filterHeapTypes(term.params[0], dtype)
        // Rewrite generic anon to correctly typed anon function
        }
        else if (term.name == "anon")
            return "(${smtdType.anon} ${filterHeapTypes(term.params[0], dtype)})"
        else
            throw Exception("${term.prettyPrint()}  is neither an heap nor anon or store function")

    }
    // Rewrite generic heap variables to correctly typed sub-heap variables
    else if(term is ProgVar && term.dType == "Heap"){
        if(term is OldHeap)
            return smtdType.old
        else if(term is LastHeap)
            return smtdType.last
        else if(term is Heap)
            return smtdType.heap
        else
            return term.name
    }
    else
        throw Exception("${term.prettyPrint()}  is neither an heap nor anon or store function")

}

data class Function(val name : String, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

    override fun toSMT(isInForm : Boolean, indent:String) : String {
        val back = getSMT(name, isInForm)

        if(name == "select") {
            val heapType = ADTRepos.libPrefix((params[1] as Field).dType)
            val fieldName = params[1].toSMT(false)
            return "(select ${filterHeapTypes(params[0], heapType)} $fieldName)"
        }

        if(params.isEmpty()) {
            if(name.startsWith("-")) return "(- ${name.substring(1)})" //CVC4 requires -1 to be passed as (- 1)
            return name
        }
        val list = params.fold("",{acc,nx -> acc + " ${nx.toSMT(isInForm)}"})
        return "($back $list)"
    }
}

data class DataTypeConst(val name : String, val dType : String, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        return name + ":" + dType+"("+params.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

    override fun toSMT(isInForm : Boolean, indent:String) : String {
        val back = getSMT(name, isInForm)
        if(params.isEmpty())
            return name
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toSMT(isInForm)}"})
        return "($back $list)"
    }

}

data class Case(val match : Term, val expectedType :String, val branches : List<BranchTerm>) : Term {
    override fun toSMT(isInForm: Boolean, indent:String): String {
        if (branches.isNotEmpty() && branches.first().matchTerm is DataTypeConst){
            val firstMatchTerm = Something(expectedType)

            val branchTerm = branches.fold(firstMatchTerm as Term, {acc:Term,branchTerm:BranchTerm  ->

                val indexOfParam = (branchTerm.matchTerm as DataTypeConst).params.indexOf(branchTerm.branch)
                if (indexOfParam != -1){
                    Ite(Exists((branchTerm.matchTerm).params.map { it as ProgVar }, Eq(match, branchTerm.matchTerm)),
                        Function("${branchTerm.matchTerm.name}_$indexOfParam", listOf(match)),acc)
                }else
                    Ite(Exists((branchTerm.matchTerm).params.map { it as ProgVar }, Eq(match, branchTerm.matchTerm)), branchTerm.branch,acc)
            })

            return branchTerm.toSMT(isInForm)
        }else
            throw Exception("Case branches with <${branches.first().matchTerm}> match terms is not supported: only DataTypeConst is supported")
    }

}

data class BranchTerm(val match : Term, val matchTerm : Term, val branch : Term) :Term {
    override fun toSMT(isInForm: Boolean, indent:String): String {
        if (matchTerm is DataTypeConst){
            val condition = Exists((matchTerm).params.map { it as ProgVar }, Eq(match, matchTerm))
            return condition.toSMT(isInForm)
        }else
            throw Exception("Case branches with <$matchTerm> match terms is not supported: only DataTypeConst is supported")
    }
}


data class UpdateOnTerm(val update : UpdateElement, val target : Term) : Term {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(isInForm : Boolean, indent:String) : String = throw Exception("Updates are not translatable to Z3")
}
data class Impl(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        return "(${left.prettyPrint()}) -> (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(isInForm : Boolean, indent:String) : String = if(isInForm) "(=> ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})" else Or(Not(left),right).toSMT(isInForm)
}
data class And(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == True) return right.prettyPrint()
        if(right == True) return left.prettyPrint()
        return "(${left.prettyPrint()}) /\\ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(isInForm : Boolean, indent:String) : String = if(isInForm) "(and ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})" else "(iAnd ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})"
}
data class Or(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == False) return right.prettyPrint()
        if(right == False) return left.prettyPrint()
        return "(${left.prettyPrint()}) \\/ (${right.prettyPrint()})"
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
    override fun toSMT(isInForm : Boolean, indent:String) : String = if(isInForm) "(or ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})" else "(iOr ${left.toSMT(isInForm)} ${right.toSMT(isInForm)})"
}
data class Not(val left : Formula) : Formula {
    override fun prettyPrint(): String {
        return "!"+left.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f)
    override fun toSMT(isInForm : Boolean, indent:String) : String = if(isInForm) "(not ${left.toSMT(isInForm)})" else "(iNot ${left.toSMT(isInForm)})"
}
data class Predicate(val name : String, val params : List<Term> = emptyList()) : Formula {
    override fun prettyPrint(): String {
        return prettyPrintFunction(params, name)
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = params.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})
    override fun toSMT(isInForm : Boolean, indent:String) : String {
        if(params.isEmpty()) return name
        val back = getSMT(name, isInForm)
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toSMT(false)}"})
        return "($back $list)"
    }
}
data class UpdateOnFormula(val update : UpdateElement, val target : Formula) : Formula {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + update.iterate(f) + target.iterate(f)
    override fun toSMT(isInForm : Boolean, indent:String) : String = throw Exception("Updates are not translatable to Z3")
}

data class Ite(val condition :Term, val term1 : Term, val term2 : Term) : Term{
    override fun toSMT(isInForm: Boolean, indent: String): String {
        return "(ite ${condition.toSMT(isInForm)}" +
                "\n\t\t$indent${term1.toSMT(isInForm, "$indent\t")}" +
                "\n\t\t$indent${term2.toSMT(isInForm, "$indent\t")})"
    }
}

data class Exists(val params :List<ProgVar>, val formula: Formula) : Term{
    override fun toSMT(isInForm: Boolean, indent:String): String {
        return "(exists (${params.joinToString(" ") { "(${it.name} ${ADTRepos.libPrefix(it.dType)})" }}) ${formula.toSMT(isInForm)})"
    }
}

data class Eq(val term1: Term, val term2 : Term) : Formula{
    override fun toSMT(isInForm: Boolean, indent:String): String {
        return "(= ${term1.toSMT(isInForm)} ${term2.toSMT(isInForm)})"
    }
}
object True : Formula {
    override fun prettyPrint(): String {
        return "true"
    }
    override fun toSMT(isInForm : Boolean, indent:String) : String = if(isInForm) "true" else "1"
}
object False : Formula {
    override fun prettyPrint(): String {
        return "false"
    }
    override fun toSMT(isInForm : Boolean, indent:String) : String = if(isInForm) "false" else "0"
}

val specialHeapKeywords = mapOf(OldHeap.name to OldHeap, LastHeap.name to LastHeap)

object Heap : ProgVar("heap","Heap")
object OldHeap : ProgVar("old","Heap")
object LastHeap : ProgVar("last","Heap")

fun store(field: Field, value : Term) : Function = Function("store", listOf(Heap, field, value))
fun select(field : Field) : Function = Function("select", listOf(Heap, field))
fun anon(heap : Term) : Function = Function("anon", listOf(heap))
fun poll(term : Term) : Function = Function("poll", listOf(term))
fun readFut(term : Expr) : Expr = SExpr("valueOf", listOf(term))
fun exprToTerm(input : Expr, old : Boolean=false) : Term {//todo: add check for non-field reference inside old and last
    return when(input){
        is ProgVar -> input
        is Field -> {
            if(old)
                return Function("old", listOf(select(input)))
            return select(input)
        }
        is PollExpr -> poll(exprToTerm(input.e1))
        is Const -> Function(input.name)
        is SExpr -> {
            if (specialHeapKeywords.containsKey(input.op)) {//todo: fix for last
                if (input.e.size == 1)
                    if(input.op != "old" && input.e[0] !is Field)
                        throw Exception("Complex argument ${input.e[0].prettyPrint()} not supported for keyword ${input.op}" )
                    else
                        Function(input.op, input.e.map { ex -> exprToTerm(ex, input.op == "old") })
                else
                    throw Exception("Special keyword ${input.op} must have one argument, actual arguments size:" + input.e.size)
            }
            Function(input.op, input.e.map { ex -> exprToTerm(ex, old) })
        }
        is DataTypeExpr -> {
            DataTypeConst(input.name, input.dType, input.e.map { ex -> exprToTerm(ex, old) })
        }
        is CaseExpr -> {
            val match =exprToTerm(input.match)
            Case(match, input.expectedType, input.content.map { ex -> BranchTerm(match,  exprToTerm(ex.matchTerm, old), exprToTerm(ex.branch, old)) })
        }
        else -> throw Exception("Expression cannot be converted to term: ${input.prettyPrint()} (${input.javaClass})")
    }
}

//todo: the comparisons with 1 should be removed once the Bool data type is split from Int
fun exprToForm(input : Expr, old : Boolean=false) : Formula {//todo: add check for non-field reference inside old and last
    if(input is SExpr && input.op == "&&" && input.e.size ==2 ) return And(exprToForm(input.e[0], old), exprToForm(input.e[1], old))
    if(input is SExpr && input.op == "||" && input.e.size ==2 ) return Or(exprToForm(input.e[0], old), exprToForm(input.e[1], old))
    if(input is SExpr && input.op == "->" && input.e.size ==2 ) return Impl(exprToForm(input.e[0], old), exprToForm(input.e[1], old))
    if(input is SExpr && input.op == "!" && input.e.size ==1 ) return Not(exprToForm(input.e[0]))
    if(input is SExpr && input.op == "!=") return Not(exprToForm(SExpr("=",input.e), old))

    if(input is SExpr){
        if(input.op == "old"){//todo: fix for last
            if(input.e.size == 1) {
                return exprToForm(input.e[0], true)
            }else
                throw Exception("Special keyword old must have one argument, actual arguments size:" + input.e.size)
        }
        return Predicate(input.op, input.e.map { ex -> exprToTerm(ex, old) })
    }
    if(input is Field || input is ProgVar || input is Const)
        return exprToForm(SExpr("=",listOf(input, Const("1"))), old)
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
        is DataTypeConst -> return DataTypeConst(input.name, input.dType, input.params.map { p -> subst(p, map) as Term })
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

fun getSMT(name: String, isInForm: Boolean): String{
    if(!isInForm) {
        if (name == "||") return "iOr"
        if (name == "&&") return "iAnd"
        if (name == "!")  return "iNot"
        if (name == "<")  return "iLt"
        if (name == "<=") return "iLeq"
        if (name == ">")  return "iGt"
        if (name == ">=") return "iGeq"
        if (name == "=")  return "iEq"
        if (name == "!=") return "iNeq"
    } else {
        if (name == "||") return "or"
        if (name == "&&") return "and"
        if (name == "!")  return "not"
    }
    return name
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