package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.frontend.ast.AddAddExp
import org.abs_models.frontend.ast.AndBoolExp
import org.abs_models.frontend.ast.Call
import org.abs_models.frontend.ast.DataConstructorExp
import org.abs_models.frontend.ast.DivMultExp
import org.abs_models.frontend.ast.EqExp
import org.abs_models.frontend.ast.Exp
import org.abs_models.frontend.ast.FieldUse
import org.abs_models.frontend.ast.FnApp
import org.abs_models.frontend.ast.GTEQExp
import org.abs_models.frontend.ast.GTExp
import org.abs_models.frontend.ast.GetExp
import org.abs_models.frontend.ast.IfExp
import org.abs_models.frontend.ast.IntLiteral
import org.abs_models.frontend.ast.LTEQExp
import org.abs_models.frontend.ast.LTExp
import org.abs_models.frontend.ast.MinusExp
import org.abs_models.frontend.ast.MultMultExp
import org.abs_models.frontend.ast.NegExp
import org.abs_models.frontend.ast.NewExp
import org.abs_models.frontend.ast.NotEqExp
import org.abs_models.frontend.ast.NullExp
import org.abs_models.frontend.ast.OrBoolExp
import org.abs_models.frontend.ast.SubAddExp
import org.abs_models.frontend.ast.ThisExp
import org.abs_models.frontend.ast.VarUse

fun renderExpression(expression: Expr, varSubMap: Map<String, String> = mapOf()): String {
    if (expression.absExp == null)
        return renderSimpleCrowbarExpression(expression, varSubMap) // Fallback rendering, required for pattern expressions
    else
        return renderAbsExpression(expression.absExp!!, varSubMap)
}

fun renderAbsExpression(e: Exp, m: Map<String, String>): String {
    return when (e) {
        is ThisExp         -> "this"
        is NullExp         -> "null"
        is IntLiteral      -> e.content
        is FieldUse        -> "this.${e.name}"
        is VarUse          -> if (m.containsKey(e.name)) m[e.name]!! else e.name
        is GTEQExp         -> "(${renderAbsExpression(e.left, m)} >= ${renderAbsExpression(e.right, m)})"
        is LTEQExp         -> "(${renderAbsExpression(e.left, m)} <= ${renderAbsExpression(e.right, m)})"
        is GTExp           -> "(${renderAbsExpression(e.left, m)} > ${renderAbsExpression(e.right, m)})"
        is LTExp           -> "(${renderAbsExpression(e.left, m)} < ${renderAbsExpression(e.right, m)})"
        is EqExp           -> "(${renderAbsExpression(e.left, m)} == ${renderAbsExpression(e.right, m)})"
        is NotEqExp        -> "(${renderAbsExpression(e.left, m)} != ${renderAbsExpression(e.right, m)})"
        is AddAddExp       -> "(${renderAbsExpression(e.left, m)} + ${renderAbsExpression(e.right, m)})"
        is SubAddExp       -> "(${renderAbsExpression(e.left, m)} - ${renderAbsExpression(e.right, m)})"
        is MultMultExp     -> "(${renderAbsExpression(e.left, m)} * ${renderAbsExpression(e.right, m)})"
        is DivMultExp      -> "(${renderAbsExpression(e.left, m)} / ${renderAbsExpression(e.right, m)})"
        is MinusExp        -> "-${renderAbsExpression(e.operand, m)}"
        is AndBoolExp      -> "(${renderAbsExpression(e.left, m)} && ${renderAbsExpression(e.right, m)})"
        is OrBoolExp       -> "(${renderAbsExpression(e.left, m)} || ${renderAbsExpression(e.right, m)})"
        is GetExp          -> "(${renderAbsExpression(e.pureExp, m)}).get"
        is NegExp          -> "!${renderAbsExpression(e.operand, m)}"
        is NewExp          -> "new ${e.className}(${e.paramList.map{ renderAbsExpression(it, m) }.joinToString(", ")})"
        is Call            -> "${e.methodSig.name}(${e.params.map{ renderAbsExpression(it, m) }.joinToString(", ")})"
        is IfExp           -> "(if ${renderAbsExpression(e.condExp, m)} then ${renderAbsExpression(e.thenExp, m)} else ${renderAbsExpression(e.elseExp, m)})"
        is FnApp           -> "${e.name}(${e.params.map{ renderAbsExpression(it, m) }.joinToString(", ")})"
        is DataConstructorExp -> e.dataConstructor!!.name
        else               -> throw Exception("Cannot render ABS Expression: $e")
    }
}

fun renderSimpleCrowbarExpression(e: Expr, m: Map<String, String>): String {
    return when (e) {
        is Const           -> e.name
        is ProgVar         -> if (m.containsKey(e.name)) m[e.name]!! else e.name
        is Field           -> "this." + e.name.substring(0, e.name.length - 2)
        else               -> throw Exception("Cannot render complex crowbar Expression: ${e.prettyPrint()}")
    }
}
