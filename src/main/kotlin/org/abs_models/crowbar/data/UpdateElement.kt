package org.abs_models.crowbar.data

interface UpdateElement: LogicElement {
    fun assigns(v : ProgVar) : Boolean
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to SMT-LIB")
}
object EmptyUpdate : UpdateElement {
    override fun prettyPrint(): String {
        return "empty"
    }
    override fun assigns(v : ProgVar) : Boolean = false
}
data class ChainUpdate(val left : UpdateElement, val right: UpdateElement) : UpdateElement {
    override fun prettyPrint(): String {
        return left.prettyPrint()+ "}{"+right.prettyPrint()
    }
    override fun assigns(v : ProgVar) : Boolean = left.assigns(v) || right.assigns(v)
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
}
data class ElementaryUpdate(val lhs : ProgVar, val rhs : Term) : UpdateElement {
    override fun prettyPrint(): String {
        return lhs.prettyPrint() + " := "+rhs.prettyPrint()
    }
    override fun assigns(v : ProgVar) : Boolean = lhs == v
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}