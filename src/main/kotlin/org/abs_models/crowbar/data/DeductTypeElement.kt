package org.abs_models.crowbar.data

import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.frontend.ast.Block
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model

/**
 *  A DeductType is a behavioral type in the sense of BPL.
 *  It must implement the four methods for the proof obligation scheme, i.e., the nodes per method, constructor, etc.
 */
interface DeductType: Anything {
	fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode
	fun extractInitialNode(classDecl: ClassDecl): SymbolicNode
	fun extractMainNode(model: Model): SymbolicNode
	fun extractFunctionNode(fDecl: FunctionDecl): SymbolicNode

	// ABS does not enforce a final return for Unit typed methods, but we need it to finish symbolic execution
	fun getNormalizedStatement(st : Block?): Stmt {
		var body = translateStatement(st, emptyMap())
		if(!body.hasReturn()) body = appendStmt(body, ReturnStmt(unitExpr()))
		return body
	}
}
