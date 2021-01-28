package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.BranchTerm
import org.abs_models.crowbar.data.CallExpr
import org.abs_models.crowbar.data.Case
import org.abs_models.crowbar.data.CaseExpr
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.DataTypeConst
import org.abs_models.crowbar.data.DataTypeExpr
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
        is DataTypeConst -> setOf(elem.name)
        is Case -> collectFromCase(elem)
        is BranchTerm -> collectUsedDefinitions(elem.matchTerm) + collectUsedDefinitions(elem.branch)
        else -> throw Exception("Cannot collect used definitions from term: ${elem::class.simpleName} ${elem.prettyPrint()}")
    }
}

fun collectFromCase(case: Case): Set<String> {
    val freeVars = case.freeVars
    val usedDefs = case.branches.fold(setOf<String>()) { collected, branch -> collected + collectUsedDefinitions(branch) }
    return usedDefs - freeVars
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
        is DataTypeExpr -> setOf()
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
        is CaseExpr -> {
            val branchCondition = collectBaseExpressions(exp.match, old)
            val branchContents = exp.content.map {
                collectBaseExpressions(it.matchTerm, old) + collectBaseExpressions(it.branch, old)
            }.flatten().toSet()
            branchCondition + branchContents.filter { it !is ProgVar || !exp.freeVars.contains(it.name) }
        }
        else -> throw Exception("Cannot collect base expressions from unknown expression: ${exp.prettyPrint()}")
    }
}
