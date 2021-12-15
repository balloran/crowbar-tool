package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.investigator.collectBaseExpressions

/*
These classes record the information needed for the CEG.
NodeInfo instances are annotated by the rules, so we are able to reconstruct the statements.
 */

// Abstract classes & interfaces
abstract class NodeInfo(val isAnon: Boolean, val isHeapAnon: Boolean) {
	open val isSignificantBranch = false // Indicates a proof branch showing an obligation other than the main postcondition
	open val initAfter = false // Indicates that initial state information should be rendered _after_ the node rendering
	open val smtExpressions = listOf<Term>()
	open val heapExpressions = listOf<Term>()
	abstract fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>): ReturnType
}

abstract class SigBranch(isAnon: Boolean, isHeapAnon: Boolean): NodeInfo(isAnon, isHeapAnon) {
	override val isSignificantBranch = true
}

interface LeafInfo {
	val obligations: List<Pair<String,Formula>>
}

// Significant branches
class InfoInvariant(invariant: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Object invariant", invariant))
}

class InfoLoopInitial(val guard: Expr, loopInv: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Loop invariant", loopInv))
}

class InfoLoopPreserves(val guard: Expr, val loopInv: Formula) : SigBranch(isAnon = true, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoClassPrecondition(precondition: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Class precondition", precondition))
}

class InfoMethodPrecondition(precondition: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Method precondition", precondition))
}

class InfoNullCheck(condition: Formula) : LeafInfo, SigBranch(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Null-check", condition))
}

// Other rule applications
class NoInfo : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoScopeClose : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoAwaitUse(val guard: Expr, val heapExpr: Term) : NodeInfo(isAnon = false, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val heapExpressions = listOf(heapExpr)
}

class InfoLoopUse(val guard: Expr, val invariant: Formula) : NodeInfo(isAnon = true, isHeapAnon = true) {
	override val initAfter = true
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoIfThen(val guard: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoIfElse(val guard: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoBranch(val matchExpr: Expr, val pattern: Expr, val previousConditions: Formula) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoLocAssign(val lhs: Location, val expression: Expr) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoGetAssign(val lhs: Location, val expression: Expr, val futureExpr: Term) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val smtExpressions = listOf(futureExpr)
}

class InfoCallAssign(val lhs: Location, val callee: Expr, val call: CallExpr, val futureName: String) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoSyncCallAssign(val lhs: Location, val callee: Expr, val call: SyncCallExpr, val heapExpr: Term, val returnValExpr: Term) : NodeInfo(isAnon = false, isHeapAnon = true) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val smtExpressions = listOf(returnValExpr)
	override val heapExpressions = listOf(heapExpr)
}

class InfoObjAlloc(val lhs: Location, val classInit: Expr, val newSMTExpr: String) : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoReturn(val expression: Expr, postcondition: Formula, invariant: Formula, update: UpdateElement) : LeafInfo, NodeInfo(isAnon = false, isHeapAnon = false) {
	val retExpr = apply(update, exprToTerm(expression)) as Term
	val retExprComponentMap = collectBaseExpressions(expression).associateWith { (apply(update, exprToTerm(it)) as Term) }
	
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Method postcondition", postcondition), Pair("Object invariant", invariant))
	override val smtExpressions = listOf(retExpr) + retExprComponentMap.values
}

class InfoSkip : NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
}

class InfoSkipEnd(postcondition: Formula) : LeafInfo, NodeInfo(isAnon = false, isHeapAnon = false) {
	override fun <ReturnType> accept(visitor: NodeInfoVisitor<ReturnType>) = visitor.visit(this)
	override val obligations = listOf(Pair("Loop invariant", postcondition))
}

interface NodeInfoVisitor<ReturnType> {
    fun visit(info: InfoAwaitUse): ReturnType
    fun visit(info: InfoBranch): ReturnType
    fun visit(info: InfoCallAssign): ReturnType
    fun visit(info: InfoClassPrecondition): ReturnType
    fun visit(info: InfoGetAssign): ReturnType
    fun visit(info: InfoIfElse): ReturnType
    fun visit(info: InfoIfThen): ReturnType
    fun visit(info: InfoInvariant): ReturnType
    fun visit(info: InfoLocAssign): ReturnType
    fun visit(info: InfoLoopInitial): ReturnType
    fun visit(info: InfoLoopPreserves): ReturnType
    fun visit(info: InfoLoopUse): ReturnType
    fun visit(info: InfoMethodPrecondition): ReturnType
    fun visit(info: InfoNullCheck): ReturnType
    fun visit(info: InfoObjAlloc): ReturnType
    fun visit(info: InfoReturn): ReturnType
    fun visit(info: InfoScopeClose): ReturnType
    fun visit(info: InfoSkip): ReturnType
    fun visit(info: InfoSkipEnd): ReturnType
    fun visit(info: InfoSyncCallAssign): ReturnType
    fun visit(info: NoInfo): ReturnType
}