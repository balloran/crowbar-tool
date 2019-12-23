package org.abs_models.crowbar.data

interface LogicElement: Anything {
    fun getFields() : Set<Field>
    fun getProgVars() : Set<ProgVar>
    fun toZ3() : String
}
interface Formula: LogicElement
interface Term : LogicElement
//interface LogicVariable : Term //for FO

val binaries = listOf(">=","<=","<",">","=","!=","+","-","*","/")

data class FormulaAbstractVar(val name : String) : Formula, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
    override fun getFields() : Set<Field> = emptySet()
    override fun getProgVars() : Set<ProgVar> = emptySet()
    override fun toZ3() : String = name
}

data class Function(val name : String, val params : List<Term> = emptyList()) : Term {
    override fun prettyPrint(): String {
        if(params.isEmpty()) return name
        if(binaries.contains(name) && params.size == 2) return params[0].prettyPrint() + name + params[1].prettyPrint()
        return name+"("+params.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
    }
    override fun getFields() : Set<Field> = params.fold(emptySet(),{ acc, nx -> acc + nx.getFields()})
    override fun getProgVars() : Set<ProgVar> = params.fold(emptySet(),{ acc, nx -> acc + nx.getProgVars()})
    override fun toZ3() : String {
        if(params.isEmpty()) return name
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toZ3()}"})
        return "($name $list)"
    }
}
data class UpdateOnTerm(val update : UpdateElement, val target : Term) : Term {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun getFields() : Set<Field> = update.getFields()+target.getFields()
    override fun getProgVars() : Set<ProgVar> = update.getProgVars()+target.getProgVars()
    override fun toZ3() : String = throw Exception("Updates are not translatable to Z3")
}
data class Impl(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        return "(${left.prettyPrint()}) -> (${right.prettyPrint()})"
    }
    override fun getFields() : Set<Field> = left.getFields()+right.getFields()
    override fun getProgVars() : Set<ProgVar> = left.getProgVars()+right.getProgVars()
    override fun toZ3() : String = "(=> ${left.toZ3()} ${right.toZ3()})"
}
data class And(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == True) return right.prettyPrint()
        if(right == True) return left.prettyPrint()
        return "(${left.prettyPrint()}) /\\ (${right.prettyPrint()})"
    }
    override fun getFields() : Set<Field> = left.getFields()+right.getFields()
    override fun getProgVars() : Set<ProgVar> = left.getProgVars()+right.getProgVars()
    override fun toZ3() : String = "(and ${left.toZ3()} ${right.toZ3()})"
}
data class Or(val left : Formula, val right : Formula) : Formula {
    override fun prettyPrint(): String {
        if(left == False) return right.prettyPrint()
        if(right == False) return left.prettyPrint()
        return "(${left.prettyPrint()}) \\/ (${right.prettyPrint()})"
    }
    override fun getFields() : Set<Field> = left.getFields()+right.getFields()
    override fun getProgVars() : Set<ProgVar> = left.getProgVars()+right.getProgVars()
    override fun toZ3() : String = "(or ${left.toZ3()} ${right.toZ3()})"
}
data class Not(val left : Formula) : Formula {
    override fun prettyPrint(): String {
        return "!"+left.prettyPrint()
    }
    override fun getFields() : Set<Field> = left.getFields()
    override fun getProgVars() : Set<ProgVar> = left.getProgVars()
    override fun toZ3() : String = "(not ${left.toZ3()})"
}
data class Predicate(val name : String, val params : List<Term> = emptyList()) : Formula {
    override fun prettyPrint(): String {
        if(params.isEmpty()) return name
        if(binaries.contains(name) && params.size == 2) return params[0].prettyPrint() + name + params[1].prettyPrint()
        return name+"("+params.map { p -> p.prettyPrint() }.fold("", { acc, nx -> "$acc,$nx" }).removePrefix(",") + ")"
    }
    override fun getFields() : Set<Field> = params.fold(emptySet(),{ acc, nx -> acc + nx.getFields()})
    override fun getProgVars() : Set<ProgVar> = params.fold(emptySet(),{ acc, nx -> acc + nx.getProgVars()})
    override fun toZ3() : String {
        if(params.isEmpty()) return name
        val list = params.fold("",{acc,nx -> acc+ " ${nx.toZ3()}"})
        return "($name $list)"
    }
}
data class UpdateOnFormula(val update : UpdateElement, val target : Formula) : Formula {
    override fun prettyPrint(): String {
        return "{"+update.prettyPrint()+"}"+target.prettyPrint()
    }
    override fun getFields() : Set<Field> = update.getFields()+target.getFields()
    override fun getProgVars() : Set<ProgVar> = update.getProgVars()+target.getProgVars()
    override fun toZ3() : String = throw Exception("Updates are not translatable to Z3")
}
object True : Formula {
    override fun prettyPrint(): String {
        return "true"
    }
    override fun getFields() : Set<Field> = emptySet()
    override fun getProgVars() : Set<ProgVar> = emptySet()
    override fun toZ3() : String = "true"
}
object False : Formula {
    override fun prettyPrint(): String {
        return "false"
    }
    override fun getFields() : Set<Field> = emptySet()
    override fun getProgVars() : Set<ProgVar> = emptySet()
    override fun toZ3() : String = "false"
}

object Heap : ProgVar("heap"){
    override fun getProgVars() : Set<ProgVar> = emptySet()
}
fun store(field: Field, value : Term) : Function = Function("store", listOf(Heap, field, value))
fun select(field : Field) : Function = Function("select", listOf(Heap, field))
fun anon(heap : Term) : Function = Function("anon", listOf(heap))
fun poll(term : Term) : Function = Function("poll", listOf(term))
fun readFut(term : Expr) : Expr = SExpr("read", listOf(term))

fun exprToTerm(input : Expr) : Term {
    if(input is ProgVar) return input
    if(input is Field) return select(input)
    if(input is AddExpr) return Function("+", listOf(exprToTerm(input.e1), exprToTerm(input.e2)))
    if(input is PollExpr) return poll(exprToTerm(input.e1))
    if(input is Const) return Function(input.name)
    if(input is SExpr) return Function(input.op, input.e.map { ex -> exprToTerm(ex) })
    throw Exception("Expression cannot be converted to term: "+input.prettyPrint())
}

fun exprToForm(input : Expr) : Formula {
    if(input is SExpr && input.op == "&&" && input.e.size ==2 ) return And(exprToForm(input.e[0]), exprToForm(input.e[1]))
    if(input is SExpr && input.op == "||" && input.e.size ==2 ) return Or(exprToForm(input.e[0]), exprToForm(input.e[1]))
    if(input is SExpr && input.op == "->" && input.e.size ==2 ) return Impl(exprToForm(input.e[0]), exprToForm(input.e[1]))
    if(input is SExpr && input.op == "!" && input.e.size ==1 ) return Not(exprToForm(input.e[0]))
    if(input is SExpr) return Predicate(input.op, input.e.map { ex -> exprToTerm(ex) })
    throw Exception("Expression cannot be converted to formula: "+input.prettyPrint())
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
        else                -> input
    }
}

fun apply(update: UpdateElement, input: LogicElement) : LogicElement {
    return when(update) {
        is EmptyUpdate -> input
        is ElementaryUpdate -> subst(input, update.lhs, update.rhs)
        is ChainUpdate -> apply(update.left, apply(update.right, input))
        else                -> input
    }
}

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