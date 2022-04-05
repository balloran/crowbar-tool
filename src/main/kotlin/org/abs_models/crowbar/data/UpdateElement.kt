package org.abs_models.crowbar.data

/**
 *  Data structures for updates
 */

interface UpdateElement: LogicElement {
    fun assigns(v : ProgVar) : Boolean
    override fun toSMT(indent:String) : String = throw Exception("Updates are not translatable to SMT-LIB")
}
object EmptyUpdate : UpdateElement {
    override fun prettyPrint(): String ="empty"
    override fun assigns(v : ProgVar) : Boolean = false
}
data class ChainUpdate(val left : UpdateElement, val right: UpdateElement) : UpdateElement {
    override fun prettyPrint(): String = left.prettyPrint()+ "}{"+right.prettyPrint()
    override fun assigns(v : ProgVar) : Boolean = left.assigns(v) || right.assigns(v)
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate(f) + right.iterate(f)
}
data class ElementaryUpdate(val lhs : ProgVar, val rhs : Term) : UpdateElement {
    override fun prettyPrint(): String = lhs.prettyPrint() + " := "+rhs.prettyPrint()
    override fun assigns(v : ProgVar) : Boolean = lhs == v
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + lhs.iterate(f) + rhs.iterate(f)
}

/**
 *  Abstract Updates represent abstract updates needed for abstract executions.
 */

data class AbstractUpdate(val name : ConcreteName, val accessible : AELocSet, val assignable : AELocSet) : UpdateElement{
    override fun assigns(v: ProgVar): Boolean = true
}