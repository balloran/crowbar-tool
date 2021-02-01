package org.abs_models.crowbar.data

interface LocalType : Anything {
    fun matches(pattern: LTPattern): Boolean
}

interface SingleLT : LocalType

data class LTSeq(val first: LocalType, val second: LocalType) : LocalType {
    override fun matches(pattern: LTPattern): Boolean {
        return if(first is LTRep)
            first.matches(pattern) || second.matches(pattern)
        else
            first.matches(pattern)
    }

    override fun prettyPrint(): String {
        return "${first.prettyPrint()}.${second.prettyPrint()}"
    }
}

data class LTNest(val inner: LocalType) : LocalType {
    override fun matches(pattern: LTPattern) = inner.matches(pattern)

    override fun prettyPrint(): String {
        return "(${inner.prettyPrint()})"
    }
}

data class LTOpt(val first: LocalType, val second: LocalType) : LocalType {
    override fun matches(pattern: LTPattern) = first.matches(pattern) || second.matches(pattern)

    override fun prettyPrint(): String {
        return "${first.prettyPrint()} + ${second.prettyPrint()}"
    }
}

data class LTRep(val inner: LocalType, val formula: Formula) : LocalType {
    override fun matches(pattern: LTPattern) = inner.matches(pattern)

    override fun prettyPrint(): String {
        return "${inner.prettyPrint()}*[${formula.prettyPrint()}]"
    }
}

data class LTSusp(val formula: Formula) : SingleLT {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternSusp)

    override fun prettyPrint(): String {
        return "Susp[${formula.prettyPrint()}]"
    }
}

data class LTPut(val formula: Formula) : SingleLT {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternPut)

    override fun prettyPrint(): String {
        return "Put[${formula.prettyPrint()}]"
    }
}

data class LTGet(val term: Term) : SingleLT {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternGet)

    override fun prettyPrint(): String {
        return "Get(${term.prettyPrint()})"
    }
}

data class LTCall(val role: String, val method: String, val formula: Formula) : SingleLT {
    override fun matches(pattern: LTPattern) = (pattern is LTPatternCall && pattern.method == method) 
    override fun prettyPrint(): String {
        return "$role!$method[${formula.prettyPrint()}]"
    }
}

object LTSkip : SingleLT {
    override fun matches(pattern: LTPattern) = (pattern == LTPatternSkip)
    override fun prettyPrint() = "skip"
}

interface LTPattern
object LTPatternSkip : LTPattern
object LTPatternGet : LTPattern
object LTPatternPut : LTPattern
object LTPatternSusp : LTPattern

// TODO: No role information here so far
data class LTPatternCall(val method: String) : LTPattern
