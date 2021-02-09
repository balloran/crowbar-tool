package org.abs_models.crowbar.types

import kotlin.system.exitProcess
import org.abs_models.crowbar.data.AbstractVar
import org.abs_models.crowbar.data.AllocateStmt
import org.abs_models.crowbar.data.And
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.AwaitStmt
import org.abs_models.crowbar.data.BranchAbstractListVar
import org.abs_models.crowbar.data.BranchList
import org.abs_models.crowbar.data.BranchStmt
import org.abs_models.crowbar.data.CallExpr
import org.abs_models.crowbar.data.CallExprAbstractVar
import org.abs_models.crowbar.data.CallStmt
import org.abs_models.crowbar.data.ChainUpdate
import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.data.ElementaryUpdate
import org.abs_models.crowbar.data.EmptyUpdate
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.ExprAbstractVar
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.FormulaAbstractVar
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Heap
import org.abs_models.crowbar.data.IfStmt
import org.abs_models.crowbar.data.LTCall
import org.abs_models.crowbar.data.LTGet
import org.abs_models.crowbar.data.LTPatternCall
import org.abs_models.crowbar.data.LTPatternGet
import org.abs_models.crowbar.data.LTPatternPut
import org.abs_models.crowbar.data.LTPatternRep
import org.abs_models.crowbar.data.LTPatternSusp
import org.abs_models.crowbar.data.LTPut
import org.abs_models.crowbar.data.LTRep
import org.abs_models.crowbar.data.LTSkip
import org.abs_models.crowbar.data.LTSusp
import org.abs_models.crowbar.data.LastHeap
import org.abs_models.crowbar.data.LocalType
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.LocationAbstractVar
import org.abs_models.crowbar.data.LogicElement
import org.abs_models.crowbar.data.Modality
import org.abs_models.crowbar.data.Not
import org.abs_models.crowbar.data.OldHeap
import org.abs_models.crowbar.data.PPAbstractVar
import org.abs_models.crowbar.data.Predicate
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.ReturnVar
import org.abs_models.crowbar.data.SExpr
import org.abs_models.crowbar.data.ScopeMarker
import org.abs_models.crowbar.data.SeqStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.data.StmtAbstractVar
import org.abs_models.crowbar.data.SymbolicState
import org.abs_models.crowbar.data.SyncStmt
import org.abs_models.crowbar.data.Term
import org.abs_models.crowbar.data.True
import org.abs_models.crowbar.data.UpdateElement
import org.abs_models.crowbar.data.UpdateOnFormula
import org.abs_models.crowbar.data.WhileStmt
import org.abs_models.crowbar.data.anon
import org.abs_models.crowbar.data.appendStmt
import org.abs_models.crowbar.data.apply
import org.abs_models.crowbar.data.exprToForm
import org.abs_models.crowbar.data.exprToTerm
import org.abs_models.crowbar.data.store
import org.abs_models.crowbar.data.subst
import org.abs_models.crowbar.data.valueOfFunc
import org.abs_models.crowbar.interfaces.LocalTypeParser
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.main.Verbosity
import org.abs_models.crowbar.main.extractInheritedSpec
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoBranch
import org.abs_models.crowbar.tree.InfoCallAssign
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoIfElse
import org.abs_models.crowbar.tree.InfoIfThen
import org.abs_models.crowbar.tree.InfoLocAssign
import org.abs_models.crowbar.tree.InfoLoopInitial
import org.abs_models.crowbar.tree.InfoLoopPreserves
import org.abs_models.crowbar.tree.InfoLoopUse
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.NodeInfo
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.DataConstructorExp
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.MethodImpl
import org.abs_models.frontend.ast.Model
import org.abs_models.frontend.ast.StringLiteral

// Declaration
interface LocalTypeType : DeductType {
    companion object : LocalTypeType

    override fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode {
        val mDecl = classDecl.methods.firstOrNull { it.methodSig.name == name }
        if (mDecl == null) {
            System.err.println("method not found: ${classDecl.qualifiedName}.$name")
            exitProcess(-1)
        }

        output("Crowbar  : loading specification....")
        val symb: SymbolicState?
        val objInv: Formula?
        val ltexp: LocalType?
        val metpre: Formula?
        val body: Stmt?

        try {
            objInv = extractSpec(classDecl, "ObjInv", "<UNKNOWN>")
            ltexp = extractLocalTypeSpec(mDecl)
            metpre = extractInheritedSpec(mDecl.methodSig, "Requires")
            body = getNormalizedStatement(mDecl.block)
        } catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        output("Crowbar-v: method local type expression: ${ltexp?.prettyPrint() ?: "null"}", Verbosity.V)

        // We have nothing to show if the method has no LocalType annotation
        if (ltexp == null)
            return emptySymNode()

        val updateOldHeap = ChainUpdate(ElementaryUpdate(LastHeap, Heap), ElementaryUpdate(OldHeap, Heap))
        symb = SymbolicState(And(objInv, metpre), updateOldHeap, Modality(body, LocalTypeTarget(ltexp, objInv)))

        return SymbolicNode(symb, emptyList())
    }

    fun extractLocalTypeSpec(mDecl: MethodImpl): LocalType? {
        val annotations = mDecl.nodeAnnotations.filter {
            it.type.toString().endsWith(".Spec") && it.value is DataConstructorExp && (it.value as DataConstructorExp).constructor == "LocalType"
        }.map { it.value as DataConstructorExp }

        return when (annotations.size) {
            0 -> null
            1 -> LocalTypeParser.parse((annotations[0].getParam(0) as StringLiteral).content)
            else -> throw Exception("Cannot have more than one LocalType annotation per method (at method ${mDecl.methodSig.name})")
        }
    }

    override fun extractInitialNode(classDecl: ClassDecl): SymbolicNode {
        // TODO: return static node
        return emptySymNode()
    }

    override fun exctractMainNode(model: Model) = emptySymNode()

    override fun exctractFunctionNode(fDecl: FunctionDecl) = emptySymNode()

    fun emptySymNode(): SymbolicNode {
        val emptySymState = SymbolicState(True, EmptyUpdate, Modality(SkipStmt, LocalTypeTarget(LTSkip)))
        return SymbolicNode(emptySymState, listOf())
    }
}

data class LocalTypeTarget(val lte: LocalType, val invariant: Formula = True, val showInvariant: Boolean = false) : LocalTypeType {
    override fun prettyPrint() = lte.prettyPrint()
}

data class LocalTypeAbstractTarget(val name: String) : LocalTypeType, AbstractVar {
    override fun prettyPrint(): String {
        return name
    }
}

abstract class LTTAssign(protected val repos: Repository, conclusion: Modality) : Rule(conclusion) {

    protected fun assignFor(loc: Location, rhs: Term): ElementaryUpdate {
        return if (loc is Field)
            ElementaryUpdate(Heap, store(loc, rhs))
        else
            ElementaryUpdate(loc as ProgVar, rhs)
    }

    protected fun symbolicNext(loc: Location, rhs: Term, remainder: Stmt, target: DeductType, iForm: Formula, iUp: UpdateElement, infoObj: NodeInfo): SymbolicNode {
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc, rhs)),
            Modality(remainder, target)
        ), info = infoObj)
    }
}

// Type system
class LTTLocAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val info = InfoLocAssign(lhs, rhsExpr)
        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info))
    }
}

class LTTSyncAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(SyncStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as SExpr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as LocalTypeTarget
        val ltexp = target.lte

        // We're executing a get statement here which has to match the local type specification
        if (!ltexp.matches(LTPatternGet)) {
            output("Crowbar  : Bailing out, could not match .get to ${target.prettyPrint()}")
            return listOf()
        }

        // Side condition: Show that the term we sync on is equivalent to the specified one
        val matchedGet = ltexp.getMatch(LTPatternGet) as LTGet
        val rhsTerm = exprToTerm(rhsExpr.e[0]) // rhsExpr is valueOf(<get term>)
        println(rhsExpr.e[0].prettyPrint())
        println(rhsTerm.prettyPrint())
        println(matchedGet.term.prettyPrint())
        // val termsEqual = LogicNode(input.condition, UpdateOnFormula(input.update, Predicate("=", listOf(matchedGet.term, rhsTerm))))
        val termsEqual = LogicNode(True, True) // TODO

        val newTarget = LocalTypeTarget(ltexp.readTransform(LTPatternGet), target.invariant, target.showInvariant)

        // Generate SMT representation of the future expression to get its model value later
        val futureSMTExpr = apply(input.update, rhs) as Term
        val info = InfoGetAssign(lhs, rhsExpr, futureSMTExpr)

        return listOf(symbolicNext(lhs, rhs, remainder, newTarget, input.condition, input.update, info), termsEqual)
    }
}

class LTTAllocAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(AllocateStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr) as Function
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType

        val nextRhs = Function(rhs.name, rhs.params.subList(1, rhs.params.size))

        // Generate SMT representation of the NEW expression to get its model value later
        val constructorSMTExpr = apply(input.update, nextRhs).toSMT()

        val next = symbolicNext(lhs,
                                nextRhs,
                                remainder,
                                target,
                                And(input.condition, UpdateOnFormula(input.update, Not(Predicate("=", listOf(nextRhs, Function("0")))))),
                                ChainUpdate(input.update, assignFor(lhs, nextRhs)),
                                InfoObjAlloc(lhs, rhsExpr, constructorSMTExpr))

        return listOf(next)
    }
}

class LTTCallAssign(repos: Repository) : LTTAssign(repos, Modality(
    SeqStmt(CallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), CallExprAbstractVar("CALL")),
        StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val calleeExpr = cond.map[ExprAbstractVar("CALLEE")] as Expr
        // val callee = exprToTerm(calleeExpr)
        val call = cond.map[CallExprAbstractVar("CALL")] as CallExpr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as LocalTypeTarget

        // We're executing a call here which has to match the local type specification
        val ltexp = target.lte
        val callPattern = LTPatternCall(call.met.split(".").last())
        if (!ltexp.matches(callPattern)) {
            output("Crowbar  : Bailing out, could not match call $callPattern to ${target.prettyPrint()}")
            return listOf()
        }

        // Side condition: Show that the role of the callee matches the specified role
        val matchedCall = ltexp.getMatch(callPattern) as LTCall
        val rolesMatch = LogicNode(True, True) // TODO: How do we do this?

        val newTarget = LocalTypeTarget(ltexp.readTransform(callPattern), target.invariant, target.showInvariant)

        val targetDecl = repos.methodReqs.getValue(call.met).second
        val freshFut = FreshGenerator.getFreshFuture(targetDecl.type.qualifiedName)
        val read = repos.methodEnss[call.met]
        val postCond = read?.first ?: True

        val targetPostDecl = read!!.second
        val substPostMap = mutableMapOf<LogicElement, LogicElement>()
        for (i in 0 until targetDecl.numParam) {
            val pName = ProgVar(targetPostDecl.getParam(i).name, targetPostDecl.getParam(i).type.qualifiedName)
            val pValue = exprToTerm(call.e[i])
            substPostMap[pName] = pValue
        }
        val substPostCond = subst(postCond, substPostMap) as Formula
        val updateNew = ElementaryUpdate(ReturnVar(targetDecl.type.qualifiedName), valueOfFunc(freshFut))

        // Side condition: Show that specified formula holds after call
        val formulaHolds = LogicNode(
            And(input.condition, UpdateOnFormula(input.update, UpdateOnFormula(updateNew, substPostCond))),
            apply(input.update, exprToForm(matchedCall.formula)) as Formula
        )

        val next = symbolicNext(lhs,
                                freshFut,
                                remainder,
                                newTarget,
                                And(input.condition, UpdateOnFormula(input.update, UpdateOnFormula(updateNew, substPostCond))),
                                input.update,
                                InfoCallAssign(lhs, calleeExpr, call, freshFut.name))

        return listOf(rolesMatch, formulaHolds, next)
    }
}

object LTTSkip : Rule(Modality(SkipStmt, LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget

        // There's nothing left to execute.
        // If the remaining local type expression does not require any further actions,
        // the proof was successful. If not, it failed.
        return if (target.lte.couldSkip && target.showInvariant)
            listOf(LogicNode(input.condition, apply(input.update, target.invariant) as Formula)) // We may have to show an invariant here (e.g. for loop invariant preservation)
        else if (target.lte.couldSkip)
            listOf(LogicNode(True, True)) // No need to show anything if we don't have to show the invariant holds
        else {
            output("Crowbar  : Bailing out, program execution completed but expected actions remain: ${target.prettyPrint()}")
            listOf()
        }
    }
}

object LTTSkipSkip : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, target)), info = InfoSkip())
        return listOf(res)
    }
}

object LTTScopeSkip : Rule(Modality(
        SeqStmt(ScopeMarker, StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, target)), info = InfoScopeClose())
        return listOf(res)
    }
}

object LTTReturn : Rule(Modality(
        ReturnStmt(ExprAbstractVar("RET")),
        LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget
        val retExpr = cond.map[ExprAbstractVar("RET")] as Expr
        val ret = exprToTerm(retExpr)
        val typeReturn = getReturnType(ret)

        // We're executing a return statement here which has to match the local type specification
        // Specifically, we have to be able to match a Put _and_ the rest of the expression must be skippable
        val ltexp = target.lte
        if (!ltexp.matches(LTPatternPut) || !ltexp.readTransform(LTPatternPut).couldSkip) {
            output("Crowbar  : Bailing out, could not match return to ${target.prettyPrint()}")
            return listOf()
        }

        // Side condition: Show that the postcondition of the Put holds
        val matchedPut = ltexp.getMatch(LTPatternPut) as LTPut

        // Show the target invariant as well if requested
        // I don't think this is ever used for return statements, but we might as well support it
        val targetFormula = if (target.showInvariant)
                And(exprToForm(matchedPut.formula), target.invariant)
            else
                exprToForm(matchedPut.formula)

        val post = LogicNode(
            input.condition,
            UpdateOnFormula(ChainUpdate(input.update, ElementaryUpdate(ReturnVar(typeReturn), ret)), targetFormula),
            info = InfoReturn(retExpr, targetFormula, True, input.update)
        )

        return listOf(post)
    }
}

object LTTIf : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
                StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {

        val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
        val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

        // then
        val guardYes = exprToForm(guardExpr)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
        val updateYes = input.update
        val typeYes = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes))

        // else
        val guardNo = Not(exprToForm(guardExpr))
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
        val updateNo = input.update
        val typeNo = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo))
        return listOf(SymbolicNode(resThen, info = InfoIfThen(guardExpr)), SymbolicNode(resElse, info = InfoIfElse(guardExpr)))
    }
}

object LTTAwait : Rule(Modality(
        SeqStmt(AwaitStmt(ExprAbstractVar("GUARD"), PPAbstractVar("PP")), StmtAbstractVar("CONT")),
        LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget

        // Generate SMT representation of the anonymized heap for future heap reconstruction
        val anonHeapExpr = apply(ChainUpdate(input.update, ElementaryUpdate(Heap, anon(Heap))), Heap) as Term

        val objInvariant = target.invariant
        val updateLastHeap = ElementaryUpdate(LastHeap, Heap)
        val newUpdate = ChainUpdate(input.update, ChainUpdate(ElementaryUpdate(Heap, anon(Heap)), updateLastHeap))
        val newInputCondition = And(
                        input.condition,
                        UpdateOnFormula(
                            newUpdate,
                            And(objInvariant, guard)
                        )
                    )

        // We're executing a return statement here which has to match the local type specification
        val ltexp = target.lte
        if (!ltexp.matches(LTPatternSusp)) {
            output("Crowbar  : Bailing out, could not match suspend to ${target.prettyPrint()}")
            return listOf()
        }

        // Side condition: Show that the postcondition of the Susp holds
        val matchedSusp = ltexp.getMatch(LTPatternSusp) as LTSusp
        val suspPost = LogicNode(newInputCondition, UpdateOnFormula(newUpdate, exprToForm(matchedSusp.formula)))

        val newTarget = LocalTypeTarget(ltexp.readTransform(LTPatternSusp), target.invariant, target.showInvariant)

        val sState = SymbolicState(newInputCondition, newUpdate, Modality(cont, newTarget))

        return listOf(suspPost, SymbolicNode(sState, info = InfoAwaitUse(guardExpr, anonHeapExpr)))
    }
}

// todo: warning: this is the throwaway variant of loop invariants
object LTTWhile : Rule(Modality(
        SeqStmt(
            WhileStmt(
                ExprAbstractVar("GUARD"),
                StmtAbstractVar("BODY"),
                PPAbstractVar("PP"),
                FormulaAbstractVar("INV")
            ),
            StmtAbstractVar("CONT")
        ),
        LocalTypeAbstractTarget("TARGET"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val guardExpr = cond.map[ExprAbstractVar("GUARD")] as Expr
        val guard = exprToForm(guardExpr)
        val body = cond.map[StmtAbstractVar("BODY")] as Stmt
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[LocalTypeAbstractTarget("TARGET")] as LocalTypeTarget

        // We're executing a loop here which has to match the local type specification
        val ltexp = target.lte
        var invariant: Formula
        var useTarget: LocalTypeTarget
        var preservesTarget: LocalTypeTarget

        // Side condition: Show that the specified invariant holds
        if (ltexp.matches(LTPatternRep)) {
            val matchedRep = ltexp.getMatch(LTPatternRep) as LTRep
            invariant = exprToForm(matchedRep.formula)
            useTarget = LocalTypeTarget(ltexp.readTransform(LTPatternRep), target.invariant, target.showInvariant)
            preservesTarget = LocalTypeTarget(matchedRep.inner, invariant, true)
        }
        // If no repetition could be matched, the proof might still succeed if the loop does nothing
        else {
            invariant = True
            useTarget = LocalTypeTarget(ltexp, target.invariant, target.showInvariant)
            preservesTarget = LocalTypeTarget(LTSkip, True, true)
        }

        // Initial Case
        val initial = LogicNode(input.condition, UpdateOnFormula(input.update, invariant), info = InfoLoopInitial(guardExpr, invariant))

        // Preserves Case
        val preservesInfo = InfoLoopPreserves(guardExpr, invariant)
        val preserves = SymbolicState(And(invariant, guard),
            EmptyUpdate,
            Modality(appendStmt(body, SeqStmt(ScopeMarker, SkipStmt)), preservesTarget)
        )

        // Use Case
        val useInfo = InfoLoopUse(guardExpr, invariant)
        val use = SymbolicState(And(invariant, Not(guard)),
                                EmptyUpdate,
                                Modality(cont, useTarget))

        return listOf(
            initial,
            SymbolicNode(preserves, info = preservesInfo),
            SymbolicNode(use, info = useInfo)
        )
    }
}

object LTTBranch : Rule(Modality(
    SeqStmt(BranchStmt(ExprAbstractVar("LHS"),
        BranchAbstractListVar("BRANCHES")), StmtAbstractVar("CONT")),
    LocalTypeAbstractTarget("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val matchExpr = cond.map[ExprAbstractVar("LHS")] as Expr
        val match = exprToTerm(matchExpr)
        val type = cond.map[LocalTypeAbstractTarget("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val branches = cond.map[BranchAbstractListVar("BRANCHES")] as BranchList
        val update = input.update
        var ress = listOf<SymbolicNode>()
        var no: Formula = True
        for (br in branches.content) {
            val preCond = Predicate("=", listOf(match, exprToTerm(br.matchTerm)))
            // Add two scope close markers for counterexample generation (one for branch, one for switch)
            val contBody = SeqStmt(br.branch, SeqStmt(ScopeMarker, SeqStmt(ScopeMarker, cont)))
            val ss = SymbolicState(And(no, And(input.condition, UpdateOnFormula(update, preCond))), update, Modality(contBody, type))
            ress = ress + SymbolicNode(ss, info = InfoBranch(matchExpr, br.matchTerm, no))
            no = And(no, Not(preCond))
        }
        return ress
    }
}
