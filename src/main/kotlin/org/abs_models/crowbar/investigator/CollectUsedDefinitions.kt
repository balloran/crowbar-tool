package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.CallExpr
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.PollExpr
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.SExpr
import org.abs_models.crowbar.data.SyncCallExpr
import org.abs_models.crowbar.data.Term

fun collectUsedDefinitions(elem: Term): Set<String> {
    return when (elem) {
        is Function -> collectFromFunction(elem)
        is ProgVar -> setOf(elem.name)
        is Field -> setOf(elem.name)
        else -> throw Exception("Cannot collect used definitions from term: ${elem.prettyPrint()}")
    }
}

fun collectFromFunction(func: Function): Set<String> {
    val paramDefs = func.params.map { collectUsedDefinitions(it) }.flatten().toSet()
    return if (func.name.startsWith("f_") || func.name.startsWith("fut_")) paramDefs + func.name else paramDefs
}

fun collectBaseExpressions(exp: Expr, old: Boolean = false): Set<Expr> {
    return when (exp) {
        is ProgVar -> setOf(exp)
        is Field -> if (old) setOf(SExpr("old", listOf(exp))) else setOf(exp)
        is PollExpr -> collectBaseExpressions(exp.e1, old)
        is Const -> setOf()
        is CallExpr -> {
            exp.e.map { collectBaseExpressions(it, old) }.flatten().toSet()
        }
        is SyncCallExpr -> {
            exp.e.map { collectBaseExpressions(it, old) }.flatten().toSet()
        }
        is SExpr -> {
            val oldflag = (exp.op == "old") || old
            exp.e.map { collectBaseExpressions(it, oldflag) }.flatten().toSet()
        }
        else -> throw Exception("Cannot collect base expressions from unknown expression: ${exp.prettyPrint()}")
    }
}
