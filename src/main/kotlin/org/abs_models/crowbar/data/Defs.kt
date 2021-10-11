package org.abs_models.crowbar.data

import java.util.*
import kotlin.reflect.KClass

//General Elements
interface Anything {
    fun prettyPrint() : String { return toString() }
    fun iterate(f: (Anything) -> Boolean) : Set<Anything> = if(f(this)) setOf(this) else emptySet()
    fun<T : Any> collectAll(clazz : KClass<T>) : Set<Anything> = iterate { clazz.isInstance(it) }
}
interface AbstractVar

data class Modality(var remainder: Stmt, val target: DeductType) : Anything {
    override fun prettyPrint() : String{ return "["+remainder.prettyPrint()+" || "+target.prettyPrint()+"]"}
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + remainder.iterate(f) + target.iterate(f)
}
data class SymbolicState(val condition: Formula, val update: UpdateElement, val modality: Modality, val exceptionScopes: List<ConcreteExceptionScope>) : Anything {
    override fun prettyPrint() : String = condition.prettyPrint()+"\n==>\n{"+update.prettyPrint()+"}"+modality.prettyPrint()+"\n exc: \n"+exceptionScopes.joinToString("; ") {it.scopes.prettyPrint()}
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = condition.iterate(f) + update.iterate(f) + modality.iterate(f) + exceptionScopes.fold( super.iterate(f)) { acc, nx -> nx.iterate(f) + acc}
}

data class ConcreteExceptionScope(val scopes : AbsBranchList, val finally : Stmt, val id : PP) : Anything {
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> =  scopes.iterate(f) + finally.iterate(f)
    override fun prettyPrint() : String = "try($id): "+ scopes.prettyPrint () + "finally: "+finally.prettyPrint()
}

open class ConcreteStringSet(val vals : Set<String> = emptySet()) : Anything

data class AbstractStringSet(val name : String) : ConcreteStringSet(), AbstractVar