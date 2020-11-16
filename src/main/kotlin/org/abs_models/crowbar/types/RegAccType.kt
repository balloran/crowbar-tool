package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.main.extractInheritedSpec
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.InferenceLeaf
import org.abs_models.crowbar.tree.SymbolicLeaf
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model
import kotlin.system.exitProcess


interface RegAcc : Anything
data class ReadAcc(val field : Field) : RegAcc{
	override fun prettyPrint() : String = "R"+field.prettyPrint()
	override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + field.iterate (f)
}
data class WriteAcc(val field : Field) : RegAcc{
	override fun prettyPrint() : String = "W"+field.prettyPrint()
	override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + field.iterate (f)
}

data class AccInferenceLeaf(val left : RegAccType, val right : RegAccType) : InferenceLeaf{
	override fun finishedExecution() : Boolean = true
	override fun debugString(steps : Int) : String = "${left.prettyPrint()} = ${right.prettyPrint()}"
	override fun collectLeaves() : List<SymbolicLeaf> = listOf(this)
	override fun evaluate() : Boolean = false
	override fun hasAbstractVar() : Boolean = left.hasAbstractVar() || right.hasAbstractVar()
	override fun normalize() = Unit
}




//Declaration
interface RegAccType : DeductType{
	companion object : RegAccType {
		override fun hasAbstractVar(): Boolean = false
	}
	override fun extractMethodNode(classDecl: ClassDecl, name : String, repos: Repository) : SymbolicNode {

		val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == name }
		if (mDecl == null) {
			System.err.println("method not found: ${classDecl.qualifiedName}.${name}")
			exitProcess(-1)
		}
		if (mDecl.methodSig.params.any { !repos.isAllowedType(it.type.toString()) }) {
			System.err.println("parameters with non-Int type not supported")
			exitProcess(-1)
		}
		val symb: SymbolicState?
		val objInv: Formula?
		val metpre: Formula?
		val body: Stmt?
		try {
			objInv = extractSpec(classDecl, "ObjInv", "<UNKNOWN>")
			metpre = extractInheritedSpec(mDecl.methodSig, "Requires")
			body = getNormalizedStatement(mDecl.block)
		} catch (e: Exception) {
			e.printStackTrace()
			System.err.println("error during translation, aborting")
			exitProcess(-1)
		}

		symb = SymbolicState(And(objInv,metpre), EmptyUpdate, Modality(body, FreshGenerator.getFreshRAVar()))
		return SymbolicNode(symb, emptyList())
	}
	override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode = throw Exception("This type is not executable")
	override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode = throw Exception("This type is not executable")
	override fun exctractMainNode(model: Model) : SymbolicNode = throw Exception("This type cannot be applied to the main block")
	fun hasAbstractVar() : Boolean // in the sense of BPL unification, not AccVar
}
data class RegAccAbstractVar(val name : String) : RegAccType, AbstractVar {
	override fun prettyPrint(): String {
		return name
	}
	override fun hasAbstractVar() : Boolean = true
}

data class AccVar(val name : String) : RegAccType{
	override fun hasAbstractVar() : Boolean = false
	override fun prettyPrint() : String = name
}
data class AccAtom(val fields : Set<RegAcc>) : RegAccType{
	override fun hasAbstractVar() : Boolean = false
	override fun prettyPrint() : String = "acc: "+fields.map { it.prettyPrint() }.toString()
	override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = fields.fold(super.iterate(f),{ acc, nx -> acc + nx.iterate(f)})

}
data class AccSeq(val first : RegAccType, val second : RegAccType) : RegAccType {
	override fun hasAbstractVar(): Boolean = first.hasAbstractVar() || second.hasAbstractVar()
	override fun prettyPrint() : String = "${first.prettyPrint()} . ${second.prettyPrint()}"
	override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + first.iterate (f) + second.iterate (f)
}
data class AccBranch(val left : RegAccType, val right : RegAccType): RegAccType {
	override fun hasAbstractVar(): Boolean = left.hasAbstractVar() || right.hasAbstractVar()
	override fun prettyPrint() : String = "${left.prettyPrint()} | ${right.prettyPrint()}"
	override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + left.iterate (f) + right.iterate (f)
}
data class AccRep(val inner : RegAccType) : RegAccType {
	override fun hasAbstractVar(): Boolean = inner.hasAbstractVar()
	override fun prettyPrint() : String = "$({inner.prettyPrint()})*"
	override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + inner.iterate (f)
}

abstract class RAAssign(conclusion : Modality) : Rule(conclusion){

	private fun assignFor(loc : Location, rhs : Term) : ElementaryUpdate{
		return if(loc is Field)   ElementaryUpdate(Heap, store(loc, rhs)) else ElementaryUpdate(loc as ProgVar, rhs)
	}
	protected fun symbolicNext(loc : Location,
	                           rhs : Term,
	                           remainder : Stmt,
	                           target : DeductType,
	                           iForm : Formula,
	                           iUp : UpdateElement) : SymbolicNode {
		return SymbolicNode(SymbolicState(
			iForm,
			ChainUpdate(iUp, assignFor(loc,rhs)),
			Modality(remainder, target)
		))
	}
}
object RAVarAssign : RAAssign(Modality(
	SeqStmt(AssignStmt(ProgAbstractVar("LHS"), ExprAbstractVar("EXPR")),
		StmtAbstractVar("CONT")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val lhs = cond.map[ProgAbstractVar("LHS")] as ProgVar
		val rhs = cond.map[ExprAbstractVar("EXPR")] as Expr
		val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
		val target = cond.map[RegAccAbstractVar("TYPE")] as RegAccType
		val myVar = FreshGenerator.getFreshRAVar()
		val infLeaf = AccInferenceLeaf(
			target,
			AccSeq(AccAtom(generateAccs(rhs)), myVar)
		)
		return listOf(infLeaf, symbolicNext(lhs, exprToTerm(rhs), remainder, myVar, input.condition, input.update))
	}
}


object RAFieldAssign : RAAssign(Modality(
	SeqStmt(AssignStmt(ProgFieldAbstractVar("LHS"), ExprAbstractVar("EXPR")),
		StmtAbstractVar("CONT")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val lhs = cond.map[ProgFieldAbstractVar("LHS")] as Field
		val rhs = cond.map[ExprAbstractVar("EXPR")] as Expr
		val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
		val target = cond.map[RegAccAbstractVar("TYPE")] as RegAccType
		val myVar = FreshGenerator.getFreshRAVar()
		val second = AccAtom(generateAccs(rhs) + WriteAcc(lhs))
		val infLeaf = AccInferenceLeaf(
			target,
			AccSeq(second, myVar)
		)
		return listOf(infLeaf, symbolicNext(lhs, exprToTerm(rhs), remainder, myVar, input.condition, input.update))
	}
}


object RAReturn : Rule(Modality(
	ReturnStmt(ExprAbstractVar("RET")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val target = cond.map[RegAccAbstractVar("TYPE")] as RegAccType
		val retExpr = cond.map[ExprAbstractVar("RET")] as Expr
		val res = AccInferenceLeaf(
			target,
			AccAtom(generateAccs(retExpr))
		)
		return listOf(res)
	}
}

object RASkip : Rule(Modality(
	SkipStmt,
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val target = cond.map[RegAccAbstractVar("TYPE")] as RegAccType
		val res = AccInferenceLeaf(
			target,
			target)

		return listOf(res)
	}
}

object RASkipSkip : Rule(Modality(
	SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
	RegAccAbstractVar("TYPE"))) {

	override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
		val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
		val ratype = cond.map[RegAccAbstractVar("TYPE")] as RegAccType
		val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, ratype)))
		return listOf(res)
	}
}


fun generateAccs(input: Expr): Set<RegAcc> {
	return input.collectAll(Field::class).map { ReadAcc(it as Field) }.toSet()
}
