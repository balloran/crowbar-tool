package org.abs_models.crowbar.data

import org.abs_models.crowbar.tree.LogicNode

interface LocalType : Anything {
    // Indicates that the subexpression can be matched to "nothing"
    val couldSkip: Boolean
    // Indicates that the subexpression can ONLY be matched to "nothing"
    val isSkip: Boolean

    val sideConditions: List<LogicNode>

    // True if the LTPattern matches a possible starting element of the pattern specified by this LocalType expression
    // E.g. in (a+b).c, a and b would be possible starting elements
    fun matches(pattern: LTPattern): Boolean

    fun getMatch(pattern: LTPattern): LocalType

    // Return a LocalType expression describing all possible runs _after_ reading the LTPattern
    // Replaces removed elements with their required side conditions (has to be called with matching context for side condition rendering)
    // E.g. for ((a.b) + (c.d)), possible runs after reading a would be "b"
    fun readTransform(pattern: LTPattern, context: LTContext = LTEmptyContext): LocalType
}

abstract class SingleLT : LocalType {
    override val couldSkip = false
    override val isSkip = false
    override val sideConditions = emptyList<LogicNode>()

    override fun getMatch(pattern: LTPattern): LocalType {
        if(!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
        return this
    }
}

abstract class CommonSidecondLT : SingleLT() {
    abstract val formula: Expr

    override fun readTransform(pattern: LTPattern, context: LTContext): LocalType {
        if (!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")

        if(context !is LTCommonContext)
            throw Exception("readTransform called with incorrect context ${context::class}, expecting LTCommonContext")

        val sidecond = LogicNode(context.cond, UpdateOnFormula(context.upd, exprToForm(formula)))
        return LTSideCondition(listOf(sidecond), "putOrSusp")
    }
}

data class LTSeq(val first: LocalType, val second: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = first.couldSkip && second.couldSkip

    override val isSkip: Boolean
        get() = first.isSkip && second.isSkip

    override val sideConditions: List<LogicNode>
        get() = first.sideConditions + second.sideConditions

    override fun matches(pattern: LTPattern): Boolean {
        return if (first.couldSkip)
            first.matches(pattern) || second.matches(pattern)
        else
            first.matches(pattern)
    }

    override fun getMatch(pattern: LTPattern): LocalType {
        return if(first.couldSkip && !first.matches(pattern))
            second.getMatch(pattern)
        else
            first.getMatch(pattern)
    }

    override fun readTransform(pattern: LTPattern, context: LTContext): LocalType {
        if (first.couldSkip && !first.matches(pattern))
            return LTSeq(LTSideCondition(first.sideConditions, "seq-agg"), second.readTransform(pattern, context))

        val transformed = first.readTransform(pattern, context)
        return if (transformed == LTSkip) second else LTSeq(transformed, second)
    }

    override fun prettyPrint(): String {
        return "(${first.prettyPrint()}.${second.prettyPrint()})"
    }
}

data class LTNest(val inner: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = inner.couldSkip
    override val isSkip: Boolean
        get() = inner.isSkip
    override val sideConditions: List<LogicNode>
        get() = inner.sideConditions

    override fun matches(pattern: LTPattern) = inner.matches(pattern)
    override fun getMatch(pattern: LTPattern) = inner.getMatch(pattern)
    override fun readTransform(pattern: LTPattern, context: LTContext) = inner.readTransform(pattern, context)

    override fun prettyPrint(): String {
        return "(${inner.prettyPrint()})"
    }
}

data class LTOpt(val first: LocalType, val second: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = first.couldSkip || second.couldSkip
    override val isSkip: Boolean
        get() = first.isSkip && second.isSkip
    override val sideConditions: List<LogicNode>
        get() = first.sideConditions + second.sideConditions // TODO: Rewrite to or? Warn?

    override fun matches(pattern: LTPattern) = first.matches(pattern) || second.matches(pattern)

    override fun getMatch(pattern: LTPattern): LocalType {
        return if(first.matches(pattern))
            first.getMatch(pattern)
        else
            second.getMatch(pattern)
    }

    override fun readTransform(pattern: LTPattern, context: LTContext): LocalType {
        // We choose to match the first branch if possible, even if both options match
        // This is not optimal in all cases, especially for complex expressions
        return if (first.matches(pattern))
            first.readTransform(pattern, context)
        else
            second.readTransform(pattern, context)
    }

    override fun prettyPrint(): String {
        return "(${first.prettyPrint()} + ${second.prettyPrint()})"
    }
}

data class LTRep(val inner: LocalType) : LocalType {
    override val couldSkip = true
    override val isSkip: Boolean
        get() = inner.isSkip
    override val sideConditions: List<LogicNode>
        get() = inner.sideConditions

    override fun matches(pattern: LTPattern) = if (pattern == LTPatternRep) true else inner.matches(pattern)

    override fun getMatch(pattern: LTPattern): LocalType {
        return if(pattern == LTPatternRep)
            this
        else
            inner.getMatch(pattern)
    }

    override fun readTransform(pattern: LTPattern, context: LTContext): LocalType {
        // If we are looking for a repetition, just remove the repetition
        // If the patter doesn't match the inner exp, also remove the repetition
        if (pattern == LTPatternRep || !inner.matches(pattern))
            return LTSkip

        // We match the repetition as long as possible, regardless of what follows it
        // This is not optimal in all cases
        val transformed = inner.readTransform(pattern, context)
        return if (transformed == LTSkip)
            this
        else
            LTSeq(transformed, this)
    }

    override fun prettyPrint(): String {
        //return "(${inner.prettyPrint()})*[${formula.prettyPrint()}]"
        return "(${inner.prettyPrint()})*"
    }
}

data class LTSusp(override val formula: Expr) : CommonSidecondLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternSusp)

    override fun prettyPrint(): String {
        return "Susp[${formula.prettyPrint()}]"
    }
}

data class LTPut(override val formula: Expr) : CommonSidecondLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternPut)

    override fun prettyPrint(): String {
        return "Put[${formula.prettyPrint()}]"
    }
}

data class LTGet(val term: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternGet)

    override fun readTransform(pattern: LTPattern, context: LTContext): LocalType {
        if (!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")

        if(context !is LTGetContext)
            throw Exception("readTransform called with incorrect context ${context::class}, expecting LTGetContext")

        val sidecond = LogicNode(
            context.cond,
            UpdateOnFormula(
                context.upd,
                exprToForm(SExpr("=", listOf(term, context.term)))
            )
        )

        return LTSideCondition(listOf(sidecond), "get")
    }

    override fun prettyPrint(): String {
        return "Get(${term.prettyPrint()})"
    }
}

data class LTCall(val role: String, val method: String, val precond: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern is LTPatternCall && pattern.method == method)

    override fun readTransform(pattern: LTPattern, context: LTContext): LocalType {
        if (!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")

        if(context !is LTCallContext)
            throw Exception("readTransform called with incorrect context ${context::class}, expecting LTCallContext")

        val sidecond = LogicNode(
            context.cond,
            UpdateOnFormula(
                context.upd,
                And(
                    exprToForm(SExpr("hasRole", listOf(context.callee, Const("\"$role\"")))),
                    subst(exprToForm(precond), context.substMap) as Formula
                )
            )
        )
        
        return LTSideCondition(listOf(sidecond), "call")
    }

    override fun prettyPrint(): String {
        return "$role!$method[${precond.prettyPrint()}]"
    }
}

object LTSkip : SingleLT() {
    override val couldSkip = true
    override val isSkip = true
    override fun matches(pattern: LTPattern) = false
    override fun readTransform(pattern: LTPattern, context: LTContext) =
        throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
    override fun prettyPrint() = "skip"
}

data class LTSideCondition(override val sideConditions: List<LogicNode>, private val source: String) : SingleLT() {
    override val couldSkip = true
    override val isSkip = true

    override fun matches(pattern: LTPattern) = false
    override fun readTransform(pattern: LTPattern, context: LTContext) =
        throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
    override fun prettyPrint() = "sidecond-$source"
}

interface LTContext
object LTEmptyContext : LTContext
data class LTCallContext(val cond: Formula, val upd: UpdateElement, val callee: Expr, val substMap: Map<LogicElement, LogicElement>) : LTContext
data class LTGetContext(val cond: Formula, val upd: UpdateElement, val term: Expr) : LTContext
data class LTCommonContext(val cond: Formula, val upd: UpdateElement) : LTContext

interface LTPattern
object LTPatternGet  : LTPattern { override fun toString() = "Get" }
object LTPatternPut  : LTPattern { override fun toString() = "Put" }
object LTPatternSusp : LTPattern { override fun toString() = "Susp" }
object LTPatternRep  : LTPattern { override fun toString() = "<any>*" }
data class LTPatternCall(val method: String) : LTPattern {
    override fun toString() = "<role>!$method"
}
