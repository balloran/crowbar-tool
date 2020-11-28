package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.And
import org.abs_models.crowbar.data.False
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.FormulaAbstractVar
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Heap
import org.abs_models.crowbar.data.Impl
import org.abs_models.crowbar.data.LastHeap
import org.abs_models.crowbar.data.Not
import org.abs_models.crowbar.data.OldHeap
import org.abs_models.crowbar.data.Or
import org.abs_models.crowbar.data.Predicate
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.True
import org.abs_models.crowbar.data.binaries

fun renderFormula(f: Formula, m: Map<String, String>): String {
    return when (f) {
        is True         -> "true"
        is False        -> "false"
        is Not          -> "!${renderFormula(f.left, m)}"
        is Or           -> "(${renderFormula(f.left, m)}) \\/ (${renderFormula(f.right, m)})"
        is And          -> "(${renderFormula(f.left, m)}) /\\ (${renderFormula(f.right, m)})"
        is Impl         -> "(${renderFormula(f.left, m)}) -> (${renderFormula(f.right, m)})"
        is Predicate    -> renderPredicate(f, m)
        is FormulaAbstractVar -> f.name
        else               -> throw Exception("Cannot render formula: ${f.prettyPrint()}")
    }
}

fun renderTerm(t: Term, m: Map<String, String>): String {
    return when (t) {
        is Function     -> renderFunction(t, m)
        is Field        -> "this.${t.name.substring(0, t.name.length - 2)}" // Strip _f suffix
        is ProgVar      -> if (m.containsKey(t.name)) m[t.name]!! else t.name
        else            -> throw Exception("Cannot render term: ${t.prettyPrint()}")
    }
}

fun renderPredicate(p: Predicate, m: Map<String, String>): String {
    return when {
        p.params.isEmpty() -> p.name
        binaries.contains(p.name) && p.params.size == 2 -> "(" + renderTerm(p.params[0], m) + p.name + renderTerm(p.params[1], m) + ")"
        else -> p.name + "(" + p.params.map { t -> renderTerm(t, m) }.joinToString(", ") + ")"
    }
}

fun renderFunction(f: Function, m: Map<String, String>): String {
    return when {
        f.params.isEmpty() -> f.name
        binaries.contains(f.name) && f.params.size == 2 -> "(" + renderTerm(f.params[0], m) + f.name + renderTerm(f.params[1], m) + ")"
        f.name == "select" && f.params.size == 2 && f.params[1] is Field -> renderSelect(f.params[0], f.params[1] as Field, m)
        else -> f.name + "(" + f.params.map { t -> renderTerm(t, m) }.joinToString(", ") + ")"
    }
}

fun renderSelect(heapTerm: Term, field: Field, m: Map<String, String>): String {
    val simpleHeapTerm = filterStores(heapTerm, field)
    val sht = simpleHeapTerm

    return when {
        sht is Heap || sht is OldHeap || sht is LastHeap ->
            renderTerm(sht, m) + "." + renderTerm(field, m).substring(5) // Pretty-printing select(heapconst, this.field) as heapconst.field
        else -> "select(${renderTerm(sht, m)}, ${renderTerm(field, m)})" // We'll keep a top-level select to emphasize heap access
    }
}

// Remove any store functions not relevant to the selected field or return value of matching store function
fun filterStores(heapTerm: Term, field: Field): Term {
    if (heapTerm is Function && heapTerm.name == "store") {
        val store = heapTerm
        val subHeap = store.params[0]
        val storeField = store.params[1]
        val value = store.params[2]

        return if (field == storeField)
            Function("store", listOf(Heap, field, value)) // replace the sub-heap term with a plain heap constant as it is irrelevant to the value
        else
            filterStores(subHeap, field)
    } else
        return heapTerm
}
