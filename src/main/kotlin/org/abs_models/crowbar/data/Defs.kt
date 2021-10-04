package org.abs_models.crowbar.data

import kotlin.reflect.KClass

//General Elements
interface Anything /*: Cloneable*/ {
   /* public override fun clone(): Any {
        return super.clone()
    }*/
    fun prettyPrint() : String { return toString() }
    fun iterate(f: (Anything) -> Boolean) : Set<Anything> = if(f(this)) setOf(this) else emptySet()
    fun<T : Any> collectAll(clazz : KClass<T>) : Set<Anything> = iterate { clazz.isInstance(it) }
}
interface AbstractVar
interface AbstractListVar

data class Modality(var remainder: Stmt, val target: DeductType) : Anything {
    override fun prettyPrint() : String{ return "["+remainder.prettyPrint()+" || "+target.prettyPrint()+"]"}
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + remainder.iterate(f) + target.iterate(f)
}
data class SymbolicState(val condition: Formula, val update: UpdateElement, val modality: Modality) : Anything {
    override fun prettyPrint() : String{ return condition.prettyPrint()+"\n==>\n{"+update.prettyPrint()+"}"+modality.prettyPrint()}
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + condition.iterate(f) + update.iterate(f) + modality.iterate(f)
}

open class ConcerteStringSet(val vals : Set<String> = emptySet()) : Anything

data class AbstractStringSet(val name : String) : ConcerteStringSet(), AbstractVar