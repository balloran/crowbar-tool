package org.abs_models.crowbar.data

import org.abs_models.crowbar.tree.LogicNode

/**
 *   These are the structures to represent local types, the calculus itself is in org.abs_models.crowbar.types.LocalTypeType.kt
 *   The parser is in org.abs_models.crowbar.interfaces.LocatTypeParser.kt
 */

interface LocalType : Anything {
    // Indicates that the subexpression can be matched to "nothing"
    val couldSkip: Boolean
    // Indicates that the subexpression can ONLY be matched to "nothing"
    val isSkip: Boolean

    val sideConditions: List<LogicNode>

    // True if the LTPattern matches a possible starting element of the pattern specified by this LocalType expression
    // E.g. in (a+b).c, a and b would be possible starting elements
    fun matches(pattern: LTPattern): Boolean

    fun getMatches(pattern: LTPattern): List<LocalType>

    // Return a LocalType expression describing all possible runs _after_ reading the LTPattern
    // Replaces removed elements with their required side conditions (has to be called with matching context for side condition rendering)
    // E.g. for ((a.b) + (c.d)), possible runs after reading a would be "b"
    // When set, the greedy flag ensures that the returned expression represents only the first matching path and that precisely one element was executed
    // this is required for loop execution as loop sideconditions cannot be stored within the expression as LTSidecondition nodes
    fun readTransform(pattern: LTPattern, context: LTContext = LTEmptyContext, greedy: Boolean = false): LocalType
}

abstract class SingleLT : LocalType {
    override val couldSkip = false
    override val isSkip = false
    override val sideConditions = emptyList<LogicNode>()

    override fun getMatches(pattern: LTPattern): List<LocalType> {
        return if(!matches(pattern))
                emptyList()
            else
                listOf(this)
    }
}

abstract class CommonSidecondLT : SingleLT() {
    abstract val formula: Expr

    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean): LocalType {
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

    override fun getMatches(pattern: LTPattern): List<LocalType> {
        return if(first.couldSkip)
            first.getMatches(pattern) + second.getMatches(pattern)
        else
            first.getMatches(pattern)
    }

    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean): LocalType {
        val firstMatches = first.matches(pattern)
        val secondMatches = second.matches(pattern)

        // If both expressions could be matched, we simulate execution of both in a new option
        return if(firstMatches && secondMatches && first.couldSkip && !greedy)
            LTOpt(
                LTSeq(first.readTransform(pattern, context), second), // Path executing the first expression
                LTSeq(LTSideCondition(first.sideConditions, "seq-agg"), second.readTransform(pattern, context)) // Path executing the second expression
            )
        else if (!firstMatches && first.couldSkip)
            LTSeq(LTSideCondition(first.sideConditions, "seq-agg"), second.readTransform(pattern, context))
        else
            LTSeq(first.readTransform(pattern, context), second)
    }

    override fun toString() = "$first.$second"
    override fun prettyPrint() = "(${first.prettyPrint()}.${second.prettyPrint()})"
}

data class LTNest(val inner: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = inner.couldSkip
    override val isSkip: Boolean
        get() = inner.isSkip
    override val sideConditions: List<LogicNode>
        get() = inner.sideConditions

    override fun matches(pattern: LTPattern) = inner.matches(pattern)
    override fun getMatches(pattern: LTPattern) = inner.getMatches(pattern)
    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean) = inner.readTransform(pattern, context, greedy)

    override fun toString() = "($inner)"
    override fun prettyPrint() = "(${inner.prettyPrint()})"
}

data class LTOpt(val first: LocalType, val second: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = first.couldSkip || second.couldSkip
    override val isSkip: Boolean
        get() = first.isSkip && second.isSkip

    // This one is sub-optimal, but in some cases we might have two valid matching paths through the expression
    // that only differ in their sideconditions
    // So here we squash the sidecondtions of each branch into a single formula and then show that one of the branches
    // is universally true
    override val sideConditions: List<LogicNode>
        get() : List<LogicNode> {
            if(first.sideConditions.isEmpty() || second.sideConditions.isEmpty())
                return emptyList()

            // This is a linear reduction, a binary-tree like thing would arguably be nicer
            val firstAggNode = first.sideConditions.map{ it.toFormula() }.reduce{ acc, form -> And(acc, form) }
            val secondAggNode = second.sideConditions.map{ it.toFormula() }.reduce{ acc, form -> And(acc, form) }
            return listOf(LogicNode(True, Or(firstAggNode, secondAggNode)))
        }

    override fun matches(pattern: LTPattern) = first.matches(pattern) || second.matches(pattern)

    override fun getMatches(pattern: LTPattern): List<LocalType> {
        return first.getMatches(pattern) + second.getMatches(pattern)
    }

    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean): LocalType {
        return when {
            // If both branches match, we simulate execution in both branches and keep the option
            first.matches(pattern) && second.matches(pattern) && !greedy -> 
                LTOpt(first.readTransform(pattern, context), second.readTransform(pattern, context))
            // If only one branch matches, we can throw the other away, including sideconditions
            first.matches(pattern) -> first.readTransform(pattern, context)
            else -> second.readTransform(pattern, context)
        }
    }

    override fun toString() = "($first + $second)"
    override fun prettyPrint() = "(${first.prettyPrint()} + ${second.prettyPrint()})"
}

data class LTRep(val inner: LocalType) : LocalType {
    override val couldSkip = true
    override val isSkip: Boolean
        get() = inner.isSkip
    override val sideConditions: List<LogicNode>
        get() = inner.sideConditions

    override fun matches(pattern: LTPattern) = if (pattern == LTPatternRep) true else inner.matches(pattern)

    override fun getMatches(pattern: LTPattern): List<LocalType> {
        return if(pattern == LTPatternRep)
            listOf(this)
        else
            inner.getMatches(pattern)
    }

    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean): LocalType {
        return when {
            pattern == LTPatternRep -> this // Leave the repetition in to allow tail duplication (ie statements outside the program loop still matching the repetition)
            !inner.matches(pattern) -> LTSkip
            else -> LTSeq(inner.readTransform(pattern, context), this) // Start matching one repetition body, keep repetition around
        }
    }

    override fun toString() = "($inner)*" 
    override fun prettyPrint() = "(${inner.prettyPrint()})*"
}

data class LTSusp(override val formula: Expr) : CommonSidecondLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternSusp)

    override fun toString() = "Susp"
    override fun prettyPrint() = "Susp[${formula.prettyPrint()}]"
}

data class LTPut(override val formula: Expr) : CommonSidecondLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternPut)

    override fun toString() = "Put"
    override fun prettyPrint() = "Put[${formula.prettyPrint()}]"
}

data class LTGet(val term: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternGet)

    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean): LocalType {
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

    override fun toString() = "Get"
    override fun prettyPrint() = "Get(${term.prettyPrint()})"
}

data class LTCall(val role: String, val method: String, val precond: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern is LTPatternCall && pattern.method == method)

    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean): LocalType {
        if (!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")

        if(context !is LTCallContext)
            throw Exception("readTransform called with incorrect context ${context::class}, expecting LTCallContext")

        val sidecond = LogicNode(
            context.cond,
            UpdateOnFormula(
                context.upd,
                And(
                    exprToForm(SExpr("hasRole", listOf(context.callee, Const("\"$role\"", null)))),
                    subst(exprToForm(precond), context.substMap) as Formula
                )
            )
        )
        
        return LTSideCondition(listOf(sidecond), "call")
    }

    override fun toString() = "$role!$method"
    override fun prettyPrint() = "$role!$method[${precond.prettyPrint()}]"
}

object LTSkip : SingleLT() {
    override val couldSkip = true
    override val isSkip = true
    override fun matches(pattern: LTPattern) = false
    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean) =
        throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
    override fun toString() = "skip"
    override fun prettyPrint() = "skip"
}

data class LTSideCondition(override val sideConditions: List<LogicNode>, private val source: String) : SingleLT() {
    override val couldSkip = true
    override val isSkip = true

    override fun matches(pattern: LTPattern) = false
    override fun readTransform(pattern: LTPattern, context: LTContext, greedy: Boolean) =
        throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
    override fun toString() = "sidecond"
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
