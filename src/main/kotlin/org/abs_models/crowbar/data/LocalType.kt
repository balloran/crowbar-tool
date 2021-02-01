package org.abs_models.crowbar.data

interface LocalType : Anything

data class LTSeq(val first: LocalType, val second: LocalType) : LocalType {
    override fun prettyPrint(): String {
        return "${first.prettyPrint()}.${second.prettyPrint()}"
    }
}

data class LTNest(val inner: LocalType) : LocalType {
    override fun prettyPrint(): String {
        return "(${inner.prettyPrint()})"
    }
}

data class LTOpt(val first: LocalType, val second: LocalType) : LocalType {
    override fun prettyPrint(): String {
        return "${first.prettyPrint()} + ${second.prettyPrint()}"
    }
}

data class LTRep(val inner: LocalType, val formula: Formula) : LocalType {
    override fun prettyPrint(): String {
        return "${inner.prettyPrint()}*[${formula.prettyPrint()}]"
    }
}

data class LTSusp(val formula: Formula) : LocalType {
    override fun prettyPrint(): String {
        return "Susp[${formula.prettyPrint()}]"
    }
}

data class LTPut(val formula: Formula) : LocalType {
    override fun prettyPrint(): String {
        return "Put[${formula.prettyPrint()}]"
    }
}

data class LTGet(val term: Term) : LocalType {
    override fun prettyPrint(): String {
        return "Get(${term.prettyPrint()})"
    }
}

data class LTCall(val role: String, val method: String, val formula: Formula) : LocalType {
    override fun prettyPrint(): String {
        return "$role!$method[${formula.prettyPrint()}]"
    }
}

class LTSkip() : LocalType {
    override fun prettyPrint() = "skip"
}
