package org.abs_models.crowbar.data

import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.LocalTypeTarget
import org.abs_models.frontend.ast.Block
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model

interface DeductType: Anything {
	fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode
	fun extractInitialNode(classDecl: ClassDecl): SymbolicNode
	fun exctractMainNode(model: Model): SymbolicNode
	fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode

	fun emptySymNode(): SymbolicNode {
		val emptySymState = SymbolicState(True, EmptyUpdate, Modality(SkipStmt, LocalTypeTarget(LTSkip, True)), listOf())
		return SymbolicNode(emptySymState, listOf())
	}
	fun getNormalizedStatement(st : Block?): Stmt {
		var body = translateStatement(st, emptyMap())
		if(!body.hasReturn()) body = appendStmt(body, ReturnStmt(unitExpr()))
		return body
	}
}
