package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.AwaitStmt
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.IfStmt
import org.abs_models.crowbar.data.ReturnStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.data.WhileStmt
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.interfaces.translateABSStmtToSymStmt
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.frontend.ast.*
import kotlin.system.exitProcess


//Declaration
interface PostInvType : DeductType{
    companion object : PostInvType
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

        output("Crowbar  : loading specification....")
        val symb: SymbolicState?
        val objInv: Formula?
        val metpost: Formula?
        val metpre: Formula?
        val body: Stmt?
        try {
            objInv = extractSpec(classDecl, "ObjInv")
            metpost = extractSpec(mDecl, "Ensures")
            metpre = extractInheritedSpec(mDecl.methodSig, "Requires")
            body = getNormalizedStatement(mDecl.block)
        } catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        output("Crowbar-v: method post-condition: ${metpost.prettyPrint()}", Verbosity.V)
        output("Crowbar-v: object invariant: ${objInv.prettyPrint()}",Verbosity.V)
        val updateOldHeap =  ChainUpdate(ElementaryUpdate(LastHeap,Heap), ElementaryUpdate(OldHeap, Heap))
        symb = SymbolicState(And(objInv,metpre), updateOldHeap, Modality(body, PostInvariantPair(metpost, objInv)))
        return SymbolicNode(symb, emptyList())
    }







    override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode {

        var body = getNormalizedStatement(classDecl.initBlock)
        for (fieldDecl in classDecl.fields){
            if(fieldDecl.hasInitExp()){
                val nextBody = AssignStmt(Field(fieldDecl.name+"_f", fieldDecl.type.simpleName), translateABSExpToSymExpr(fieldDecl.initExp))
                body = SeqStmt(nextBody,body)
            }
        }

        output("Crowbar  : loading specification....")
        val objInv: Formula?
        val objPre: Formula?
        try {
            objInv = extractSpec(classDecl, "ObjInv")
            objPre = extractSpec(classDecl, "Requires")
        } catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        if (verbosity >= Verbosity.V) {
            output("Crowbar-v: object precondition: ${objPre.prettyPrint()}")
            output("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
        }
        val symb = SymbolicState(objPre, EmptyUpdate, Modality(body, PostInvariantPair(True, objInv)))
        return SymbolicNode(symb, emptyList())
    }




    override fun exctractMainNode(model: Model) : SymbolicNode {

        if(!model.hasMainBlock()){
            System.err.println("model has no main block!")
            exitProcess(-1)
        }

        val v = appendStmt(translateABSStmtToSymStmt(model.mainBlock), SkipStmt)
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, PostInvariantPair(True, True))), emptyList())
    }


    override fun exctractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        val symb: SymbolicState?
        val funpost: Formula?
        val funpre: Formula?
        var body: Stmt? = null
        try {
            funpre = extractSpec(fDecl, "Requires")
            funpost = extractSpec(fDecl, "Ensures")
            val fDef = fDecl.functionDef
            if(fDef is BuiltinFunctionDef){
                throw Exception("error during translation, cannot handle builtin yet")
            }else if(fDef is ExpFunctionDef){
                body = ReturnStmt(translateABSExpToSymExpr(fDef.rhs))
            }
        }catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            throw e
        }
        if(body != null) {
            symb = SymbolicState(funpre, EmptyUpdate, Modality(body, PostInvariantPair(funpost, True)))
            return SymbolicNode(symb, emptyList())
        }else{
            throw Exception("error during translation of function contract")
        }
    }
}
data class PostInvAbstractVar(val name : String) : PostInvType, AbstractVar{
    override fun prettyPrint(): String {
        return name
    }
}
data class PostInvariantPair(val post : Formula, val objInvariant : Formula) : PostInvType {
    override fun prettyPrint(): String {
        return post.prettyPrint()+", "+objInvariant.prettyPrint()
    }
    override fun iterate(f: (Anything) -> Boolean) : Set<Anything> = super.iterate(f) + post.iterate (f) + objInvariant.iterate (f)
}

abstract class PITAssign(protected val repos: Repository,
                         conclusion : Modality) : Rule(conclusion){

    protected fun assignFor(loc : Location, rhs : Term) : ElementaryUpdate{
        return if(loc is Field)   ElementaryUpdate(Heap, store(loc, rhs)) else ElementaryUpdate(loc as ProgVar, rhs)
    }
    protected fun symbolicNext(loc : Location,
                     rhs : Term,
                     remainder : Stmt,
                     target : DeductType,
                     iForm : Formula,
                     iUp : UpdateElement) : SymbolicNode{
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc,rhs)),
            Modality(remainder, target)
        ))
    }
}

//Type system
class PITLocAssign(repos: Repository) : PITAssign(repos,Modality(
    SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhs = exprToTerm(cond.map[ExprAbstractVar("EXPR")] as Expr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        return listOf(symbolicNext(lhs,rhs,remainder, target, input.condition, input.update))
    }
}

class PITSyncAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(SyncStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhs = exprToTerm(cond.map[ExprAbstractVar("EXPR")] as Expr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update))
    }

}

class PITAllocAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(AllocateStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhs = exprToTerm(cond.map[ExprAbstractVar("EXPR")] as Expr) as Function
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        val classNameExpr = rhs.params[0] as Function
        val nextRhs = Function(rhs.name,rhs.params.subList(1,rhs.params.size))

        //construct precondition check of the class creation
        val precond = repos.classReqs.getValue(classNameExpr.name).first
        val targetDecl = repos.classReqs[classNameExpr.name]!!.second
        val substMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = select(Field(targetDecl.getParam(i).name+"_f", targetDecl.getParam(i).type.qualifiedName))
            val pValue = nextRhs.params[i]
            substMap[pName] = pValue
        }

        val pre = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, subst(precond, substMap) as Formula)
        )


        val next = symbolicNext(lhs,
                                            nextRhs,
                                            remainder,
                                            target,
                                            And(input.condition, UpdateOnFormula(input.update, Not(Predicate("=", listOf(nextRhs, Function("0")))))),
                                            ChainUpdate(input.update, assignFor(lhs, nextRhs)))

        return listOf(pre, next)
    }
}


class PITCallAssign(repos: Repository) : PITAssign(repos, Modality(
    SeqStmt(CallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), CallExprAbstractVar("CALL")),
        StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val callee = exprToTerm(cond.map[ExprAbstractVar("CALLEE")] as Expr)
        val call = cond.map[CallExprAbstractVar("CALL")] as CallExpr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType


        val nonenull = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, Not(Predicate("=", listOf(callee,Function("0", emptyList())))))
        )

        //construct precondition check of the call
        val precond = repos.methodReqs.getValue(call.met).first
        val targetDecl = repos.methodReqs.getValue(call.met).second
        val substMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = ProgVar(targetDecl.getParam(i).name,targetDecl.getParam(i).type.qualifiedName)
            val pValue = exprToTerm(call.e[i])
            substMap[pName] = pValue
        }
        val pre = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, subst(precond, substMap) as Formula)
        )


        val freshFut = FreshGenerator.getFreshFuture()
        val read = repos.methodEnss[call.met]
        val postCond = read?.first ?: True

        val targetPostDecl = read!!.second
        val substPostMap = mutableMapOf<LogicElement,LogicElement>()
        for(i in 0 until targetDecl.numParam){
            val pName = ProgVar(targetPostDecl.getParam(i).name,targetPostDecl.getParam(i).type.qualifiedName)
            val pValue = exprToTerm(call.e[i])
            substPostMap[pName] = pValue
        }

        val updateNew = ElementaryUpdate(ReturnVar("<UNKNOWN>"),valueOfFunc(freshFut))

        val next = symbolicNext(lhs,
                                            freshFut,
                                            remainder,
                                            target,
                                            And(input.condition, UpdateOnFormula(input.update,UpdateOnFormula(updateNew,subst(postCond, substPostMap) as Formula))),
                                            input.update)

        return listOf(nonenull,pre,next)
    }
}


class PITSyncCallAssign(repos: Repository) : PITAssign(repos, Modality(
        SeqStmt(SyncCallStmt(LocationAbstractVar("LHS"), ExprAbstractVar("CALLEE"), SyncCallExprAbstractVar("CALL")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val call = cond.map[SyncCallExprAbstractVar("CALL")] as SyncCallExpr
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[PostInvAbstractVar("TYPE")] as DeductType

        val freshVar = FreshGenerator.getFreshFunction()

        val precond = repos.syncMethodReqs.getValue(call.met).first
        val targetPreDecl = repos.syncMethodReqs.getValue(call.met).second

        val updateNew = ElementaryUpdate(ReturnVar("<UNKNOWN>"), freshVar)

        val substPreMap = mapSubstPar(call, targetPreDecl)

        //preconditions
        val first = LogicNode(
                input.condition,
                UpdateOnFormula(input.update, subst(precond, substPreMap) as Formula)
        )

        val postCond = repos.syncMethodEnss[call.met]?.first ?: True
        val targetPostDecl = repos.syncMethodEnss[call.met]!!.second
        val substPostMap = mapSubstPar(call, targetPostDecl)

        val anon = ElementaryUpdate(Heap, anon(Heap))

        //XXX handle  last here as well
        val someHeap = FreshGenerator.getFreshProgVar(Heap.dType)
        val heapUpdate = ChainUpdate(ElementaryUpdate(OldHeap,Heap), ElementaryUpdate(LastHeap,someHeap))

        val updateLeftNext = ChainUpdate(input.update, ChainUpdate(heapUpdate, ChainUpdate(anon, updateNew)))
        val updateRightNext = ChainUpdate(input.update, anon)
        val updateOnFormula =  UpdateOnFormula(updateLeftNext, subst(postCond, substPostMap) as Formula)

        val next = symbolicNext(lhs,
                freshVar,
                remainder,
                target,
                And(input.condition, updateOnFormula),
                updateRightNext)

        return listOf(first,next)
    }
}

fun mapSubstPar(callExpr: SyncCallExpr, targetDecl: MethodSig): MutableMap<LogicElement, LogicElement> {

    val substMap = mutableMapOf<LogicElement, LogicElement>()

    for (i in 0 until targetDecl.numParam) {
        val pName = ProgVar(targetDecl.getParam(i).name, targetDecl.getParam(i).type.qualifiedName)
        val pValue = exprToTerm(callExpr.e[i])
        substMap[pName] = pValue

    }
    return substMap
}

object PITSkip : Rule(Modality(
        SkipStmt,
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("POST")] as Formula
        val res = LogicNode(
                    input.condition,
                    UpdateOnFormula(input.update, target)
        )
        return listOf(res)
    }
}

object PITSkipSkip : Rule(Modality(
        SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype)))
        return listOf(res)
    }
}

object PITReturn : Rule(Modality(
        ReturnStmt(ExprAbstractVar("RET")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula
        val retExpr = exprToTerm(cond.map[ExprAbstractVar("RET")] as Expr)
        val res = LogicNode(
            input.condition,
            And(
                    UpdateOnFormula(ChainUpdate(input.update,
                        ElementaryUpdate(ReturnVar("<UNKNOWN>"), retExpr)), targetPost), //todo:hack
                    UpdateOnFormula(input.update, target)
            )
        )
        return listOf(res)
    }
}

object PITIf : Rule(Modality(
        SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
                StmtAbstractVar("CONT")),
        PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {

        //then
        val guardYes = exprToForm(cond.map[ExprAbstractVar("LHS")] as Expr)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, cond.map[StmtAbstractVar("CONT")] as Stmt)
        val updateYes = input.update
        val typeYes = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes))

        //else
        val guardNo = Not(exprToForm(cond.map[ExprAbstractVar("LHS")] as Expr))
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, cond.map[StmtAbstractVar("CONT")] as Stmt)
        val updateNo = input.update
        val typeNo = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo))
        return listOf(SymbolicNode(resThen),SymbolicNode(resElse))
    }
}


object PITAwait : Rule(Modality(
        SeqStmt(AwaitStmt(ExprAbstractVar("GUARD"),PPAbstractVar("PP")), StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"), FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guard = exprToForm(cond.map[ExprAbstractVar("GUARD")] as Expr)
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        val updateLastHeap = ElementaryUpdate(LastHeap, Heap)
        val lNode = LogicNode(input.condition, UpdateOnFormula(input.update, target))
        val sStat = SymbolicState(
                And(
                        input.condition,
                        UpdateOnFormula(
                                ChainUpdate(input.update,ChainUpdate(ElementaryUpdate(Heap,anon(Heap)),updateLastHeap)),
                                And(target,guard)
                        )
                ),
                ChainUpdate(input.update, ChainUpdate(ElementaryUpdate(Heap,anon(Heap)),updateLastHeap)),
                Modality(cont, PostInvariantPair(targetPost,target)))

        return listOf(lNode,SymbolicNode(sStat))

    }
}

//todo: warning: this is the throwaway variant of loop invariants
object PITWhile : Rule(Modality(
        SeqStmt(WhileStmt(ExprAbstractVar("GUARD"),
                          StmtAbstractVar("BODY"),
                          PPAbstractVar("PP"),
                          FormulaAbstractVar("INV")),
                StmtAbstractVar("CONT")),
        PostInvariantPair(FormulaAbstractVar("POST"),
                          FormulaAbstractVar("OBJ")))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val guard = exprToForm(cond.map[ExprAbstractVar("GUARD")] as Expr)
        val body = cond.map[StmtAbstractVar("BODY")] as Stmt
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val targetInv = cond.map[FormulaAbstractVar("INV")] as Formula
        val target = cond.map[FormulaAbstractVar("OBJ")] as Formula
        val targetPost = cond.map[FormulaAbstractVar("POST")] as Formula

        //Initial Case
        val initial = LogicNode(input.condition, UpdateOnFormula(input.update, targetInv))

        //Preserves Case
        val preserves = SymbolicState(And(targetInv,guard),
                                      EmptyUpdate,
                                      Modality(appendStmt(body,SkipStmt), PostInvariantPair(targetInv,target)))

        //Use Case
        val use = SymbolicState(And(targetInv,Not(guard)),
                                  EmptyUpdate,
                                  Modality(cont, PostInvariantPair(targetPost,target)))
        return listOf(initial,SymbolicNode(preserves),SymbolicNode(use))

    }
}


object PITBranch : Rule(Modality(
    SeqStmt(BranchStmt(ExprAbstractVar("LHS"),
        BranchAbstractListVar("BRANCHES")),StmtAbstractVar("CONT")),
    PostInvAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val match = exprToTerm(cond.map[ExprAbstractVar("LHS")] as Expr)
        val type = cond.map[PostInvAbstractVar("TYPE")] as DeductType
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val branches = cond.map[BranchAbstractListVar("BRANCHES")] as BranchList
        val update = input.update
        var ress = listOf<SymbolicNode>()
        var no : Formula = True
        for(br in branches.content){
            val preCond = Predicate("=",listOf(match, exprToTerm(br.matchTerm)))
            val ss = SymbolicState(And(no,And(input.condition, UpdateOnFormula(update, preCond))), update, Modality(SeqStmt(br.branch, cont), type))
            ress = ress + SymbolicNode(ss)
            no = And(no, Not(preCond))
        }
        return ress
    }
}
