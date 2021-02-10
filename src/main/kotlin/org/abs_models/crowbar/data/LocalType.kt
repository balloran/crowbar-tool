package org.abs_models.crowbar.data

interface LocalType : Anything {
    // Indicates that the subexpression can be matched to "nothing"
    val couldSkip: Boolean
    // Indicates that the subexpression can ONLY be matched to "nothing"
    val isSkip: Boolean

    // True if the LTPattern matches a possible starting element of the pattern specified by this LocalType expression
    // E.g. in (a+b).c, a and b would be possible starting elements
    fun matches(pattern: LTPattern): Boolean

    fun getMatch(pattern: LTPattern): LocalType

    // Return a LocalType expression describing all possible runs _after_ reading the LTPattern
    // E.g. for ((a.b) + (c.d)), possible runs after reading a would be "b"
    fun readTransform(pattern: LTPattern): LocalType
}

abstract class SingleLT : LocalType {
    override val couldSkip = false
    override val isSkip = false

    override fun getMatch(pattern: LTPattern): LocalType {
        if(!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
        return this
    }

    override fun readTransform(pattern: LTPattern): LocalType {
        if (!matches(pattern))
            throw Exception("Cannot match local type pattern '$pattern' to local type expression '${this.prettyPrint()}'")
        return LTSkip
    }
}

data class LTSeq(val first: LocalType, val second: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = first.couldSkip && second.couldSkip

    override val isSkip: Boolean
        get() = first.isSkip && second.isSkip

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

    override fun readTransform(pattern: LTPattern): LocalType {
        if (first.couldSkip && !first.matches(pattern))
            return second.readTransform(pattern)

        val transformed = first.readTransform(pattern)
        return if (transformed.isSkip) second else LTSeq(transformed, second)
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

    override fun matches(pattern: LTPattern) = inner.matches(pattern)
    override fun getMatch(pattern: LTPattern) = inner.getMatch(pattern)
    override fun readTransform(pattern: LTPattern) = inner.readTransform(pattern)

    override fun prettyPrint(): String {
        return "(${inner.prettyPrint()})"
    }
}

data class LTOpt(val first: LocalType, val second: LocalType) : LocalType {
    override val couldSkip: Boolean
        get() = first.couldSkip || second.couldSkip
    override val isSkip: Boolean
        get() = first.isSkip && second.isSkip

    override fun matches(pattern: LTPattern) = first.matches(pattern) || second.matches(pattern)

    override fun getMatch(pattern: LTPattern): LocalType {
        return if(first.matches(pattern))
            first.getMatch(pattern)
        else
            second.getMatch(pattern)
    }

    override fun readTransform(pattern: LTPattern): LocalType {
        // We choose to match the first branch if possible, even if both options match
        // This is not optimal in all cases, especially for complex expressions
        return if (first.matches(pattern))
            first.readTransform(pattern)
        else
            second.readTransform(pattern)
    }

    override fun prettyPrint(): String {
        return "(${first.prettyPrint()} + ${second.prettyPrint()})"
    }
}

data class LTRep(val inner: LocalType) : LocalType {
    override val couldSkip = true
    override val isSkip: Boolean
        get() = inner.isSkip

    override fun matches(pattern: LTPattern) = if (pattern == LTPatternRep) true else inner.matches(pattern)

    override fun getMatch(pattern: LTPattern): LocalType {
        return if(pattern == LTPatternRep)
            this
        else
            inner.getMatch(pattern)
    }

    override fun readTransform(pattern: LTPattern): LocalType {
        // If we are looking for a repetition, just remove the repetition
        // If the patter doesn't match the inner exp, also remove the repetition
        if (pattern == LTPatternRep || !inner.matches(pattern))
            return LTSkip

        // We match the repetition as long as possible, regardless of what follows it
        // This is not optimal in all cases
        val transformed = inner.readTransform(pattern)
        return if (transformed.isSkip)
            this
        else
            LTSeq(transformed, this)
    }

    override fun prettyPrint(): String {
        //return "(${inner.prettyPrint()})*[${formula.prettyPrint()}]"
        return "(${inner.prettyPrint()})*"
    }
}

data class LTSusp(val formula: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternSusp)

    override fun prettyPrint(): String {
        return "Susp[${formula.prettyPrint()}]"
    }
}

data class LTPut(val formula: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternPut)

    override fun prettyPrint(): String {
        return "Put[${formula.prettyPrint()}]"
    }
}

data class LTGet(val term: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternGet)

    override fun prettyPrint(): String {
        return "Get(${term.prettyPrint()})"
    }
}

data class LTCall(val role: String, val method: String, val formula: Expr) : SingleLT() {
    override fun matches(pattern: LTPattern) = (pattern is LTPatternCall && pattern.method == method)
    override fun prettyPrint(): String {
        return "$role!$method[${formula.prettyPrint()}]"
    }
}

object LTSkip : SingleLT() {
    override val couldSkip = true
    override val isSkip = true
    override fun matches(pattern: LTPattern) = (pattern == LTPatternSkip)
    override fun prettyPrint() = "skip"
}

interface LTPattern
object LTPatternSkip : LTPattern { override fun toString() = "Skip" }
object LTPatternGet  : LTPattern { override fun toString() = "Get" }
object LTPatternPut  : LTPattern { override fun toString() = "Put" }
object LTPatternSusp : LTPattern { override fun toString() = "Susp" }
object LTPatternRep  : LTPattern { override fun toString() = "<any>*" }

// TODO: No role information here so far
data class LTPatternCall(val method: String) : LTPattern {
    override fun toString() = "<role>!$method"
}
