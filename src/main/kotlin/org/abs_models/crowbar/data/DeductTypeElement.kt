package org.abs_models.crowbar.data

import org.abs_models.crowbar.interfaces.translateABSStmtToSymStmt
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.frontend.ast.Block
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model

//each type T : DeductType needs to have an object added with  "companion object : T" until I come up with something to pass around types without reflection
interface DeductType: Anything {
	fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode
	fun extractInitialNode(classDecl: ClassDecl): SymbolicNode
	fun exctractMainNode(model: Model): SymbolicNode
	fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode

	fun getNormalizedStatement(st : Block?): Stmt {
		var body = translateABSStmtToSymStmt(st, emptyMap())
		if(!body.hasReturn()) body = appendStmt(body, ReturnStmt(unitExpr()))
		return body
	}
}
data class DeductAbstractVar(val name : String) : DeductType, AbstractVar{
	override fun extractMethodNode(classDecl: ClassDecl, name : String, repos: Repository) : SymbolicNode = throw Exception("This type is not executable")
	override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode = throw Exception("This type is not executable")
	override fun exctractMainNode(model: Model) : SymbolicNode = throw Exception("This type is not executable")
	override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode = throw Exception("This type is not executable")
}
