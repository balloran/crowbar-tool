package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.IfStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.interfaces.translateExpression
import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.rule.MatchCondition
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.UnknownType
import kotlin.system.exitProcess


/**
 * DeductType for abstract Execution, lots of things to do
 */

interface AbstractType : DeductType{
    companion object : AbstractType

    /**
     * Return the emptiest possible node just for programming purpose, might change/disappear in the future.
     */

    fun totallyEmptyNode() : SymbolicNode{
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(SkipStmt, EmptyAbstractType), listOf()))
    }

    override fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode{
        return totallyEmptyNode()
    }

    /**
     * For now, extractInitialNode is the same as in PostInvType, we don't consider abstract init of classes (for now?)
     */

    override fun extractInitialNode(classDecl: ClassDecl) : SymbolicNode {

        var body = getNormalizedStatement(classDecl.initBlock)
        for (fieldDecl in classDecl.fields){
            if(fieldDecl.hasInitExp()){
                val nextBody = AssignStmt(Field(fieldDecl.name+"_f", fieldDecl.type),
                    translateExpression(fieldDecl.initExp, UnknownType.INSTANCE, emptyMap())
                )
                body = SeqStmt(nextBody,body)
            }
        }

        output("Crowbar  : loading specification....")
        val objInv: Formula?
        val objPre: Formula?
        try {
            objInv = extractSpec(classDecl, "ObjInv", UnknownType.INSTANCE)
            objPre = extractSpec(classDecl, "Requires", UnknownType.INSTANCE)
        } catch (e: Exception) {
            e.printStackTrace()
            System.err.println("error during translation, aborting")
            exitProcess(-1)
        }
        if (verbosity >= Verbosity.V) {
            output("Crowbar-v: object precondition: ${objPre.prettyPrint()}")
            output("Crowbar-v: object invariant: ${objInv.prettyPrint()}")
        }
        val symb = SymbolicState(objPre, EmptyUpdate, Modality(body, PostInvariantPair(True, objInv)), listOf())
        return SymbolicNode(symb, emptyList())
    }

    override fun extractMainNode(model: Model): SymbolicNode {

        if(!model.hasMainBlock()){
            System.err.println("model has no main block!")
            exitProcess(-1)
        }

        // A bit dirty as already called in, going to have to find a better solution
        val mainSpec = extractGlobalSpec(model.mainBlock)
        model.mainBlock.annotationList = List()

        //output("${model.mainBlock}")

        val v = appendStmt(translateStatement(model.mainBlock, emptyMap()), SkipStmt)
        //output("\n$v")
        output("\n${v.prettyPrint()}")
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, AbstractPost(mainSpec.second)), listOf()), emptyList())
    }

    override fun extractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        return totallyEmptyNode()
    }

}

object EmptyAbstractType : AbstractType{

}

data class AbstractAbstractVar(val name : String) : AbstractType, AbstractVar{
    override fun prettyPrint(): String = name
}

data class AbstractPost(val post : Formula) : AbstractType{
    override fun prettyPrint(): String = post.prettyPrint()

    override fun iterate(f: (Anything) -> Boolean): Set<Anything> = super.iterate(f) + post.iterate(f)
}

class AESimpleAbstractAssign(val repos: Repository) : Rule(Modality(
    SeqStmt(AEStmt(AbstractName("P"), LocationAbstractVar("ASSIGN"), LocationAbstractVar("ACCESS"), ExprAbstractVar("NORM"),ExprAbstractVar("RET")), StmtAbstractVar("CONT")),
    AbstractAbstractVar("TYPE"))){

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        return listOf(SymbolicNode(
            SymbolicState(
                input.condition,
                ChainUpdate(input.update, AbstractUpdate(
                    cond.map[AbstractName("P")] as ConcreteName,
                    // Here you're gonna use repository to generalize the locset according to the irrelevance rules
                    // A priori no need for partial updatify if I build the rule well
                    cond.map[LocationAbstractVar("ASSIGN")] as AELocSet,
                    cond.map[LocationAbstractVar("ACCESS")] as AELocSet)),
                Modality(
                    cond.map[StmtAbstractVar("CONT")] as Stmt,
                    cond.map[AbstractAbstractVar("TYPE")] as AbstractType),
                input.exceptionScopes),
            info = NoInfo()))
    }
}


abstract class AEAssign(protected val repos: Repository,
                         conclusion : Modality) : Rule(conclusion){

    protected fun assignFor(loc : Location, rhs : Term) : ElementaryUpdate{
        return if(loc is Field)   ElementaryUpdate(Heap, store(loc, rhs)) else ElementaryUpdate(loc as ProgVar, rhs)
    }

    protected fun symbolicNext(loc : Location,
                               rhs : Term,
                               remainder : Stmt,
                               target : DeductType,
                               iForm : Formula,
                               iUp : UpdateElement,
                               infoObj: NodeInfo,
                               scopes: List<ConcreteExceptionScope>) : SymbolicNode{
        return SymbolicNode(SymbolicState(
            iForm,
            ChainUpdate(iUp, assignFor(loc,rhs)),
            Modality(remainder, target),
            scopes
        ), info = infoObj)
    }
}

class AELocAssign(repos: Repository, val classdecl : String) : PITAssign(repos, Modality(
    SeqStmt(AssignStmt(LocationAbstractVar("LHS"), ExprAbstractVar("EXPR")), StmtAbstractVar("CONT")),
    AbstractAbstractVar("TYPE"))
){

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val lhs = cond.map[LocationAbstractVar("LHS")] as Location
        val rhsExpr = cond.map[ExprAbstractVar("EXPR")] as Expr
        val rhs = exprToTerm(rhsExpr)
        val remainder = cond.map[StmtAbstractVar("CONT")] as Stmt
        val target = cond.map[AbstractAbstractVar("TYPE")] as DeductType
        val info = InfoLocAssign(lhs, rhsExpr)
        val zeros  = divByZeroNodes(listOf(rhsExpr), remainder, input, repos)
        //output("\n$lhs\n $rhsExpr\n $rhs\n $remainder\n $target\n $info\n $zeros\n")

        if(!repos.classFrames[classdecl]!!.containsKey(lhs)){
            // Extend framing informations with this new variable
            for(loc in repos.classFrames[classdecl]!!.keys){
                if(loc is AELocation) {
                    repos.classFrames[classdecl]?.set(
                        loc,
                        AELocSet(
                            (repos.classFrames[classdecl]?.get(loc)?.locs?.plus(Pair(false, lhs))!!)
                        )
                    )
                }
            }

            repos.classFrames[classdecl]!![lhs] = AELocSet(repos.classFrames[classdecl]!!.keys.filterIsInstance<AELocation>()
                .map { loc -> Pair(false, loc) })


        }

        return listOf(symbolicNext(lhs, rhs, remainder, target, input.condition, input.update, info, input.exceptionScopes)) + zeros
    }
}

class AEIf(val repos : Repository): Rule(Modality(
    SeqStmt(IfStmt(ExprAbstractVar("LHS"), StmtAbstractVar("THEN"), StmtAbstractVar("ELSE")),
        StmtAbstractVar("CONT")),
    AbstractAbstractVar("TYPE"))){

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val contBody = SeqStmt(ScopeMarker, cond.map[StmtAbstractVar("CONT")] as Stmt) // Add a ScopeMarker statement to detect scope closure
        val guardExpr = cond.map[ExprAbstractVar("LHS")] as Expr

        //then
        val guardYes = exprToForm(guardExpr)
        val guardYesUpdate = extractUpdateFromForm(guardYes)
        val bodyYes = SeqStmt(cond.map[StmtAbstractVar("THEN")] as Stmt, contBody)
        val updateYes = ChainUpdate(input.update, guardYesUpdate)
        val typeYes = cond.map[AbstractAbstractVar("TYPE")] as AbstractType
        val resThen = SymbolicState(And(input.condition, UpdateOnFormula(updateYes, guardYes)), updateYes, Modality(bodyYes, typeYes), input.exceptionScopes)

        //else
        val guardNo = Not(exprToForm(guardExpr))
        val guardNoUpdate = extractUpdateFromForm(guardNo)
        val bodyNo = SeqStmt(cond.map[StmtAbstractVar("ELSE")] as Stmt, contBody)
        val updateNo = ChainUpdate(input.update, guardNoUpdate)
        val typeNo = cond.map[AbstractAbstractVar("TYPE")] as AbstractType
        val resElse = SymbolicState(And(input.condition, UpdateOnFormula(updateNo, guardNo)), updateNo, Modality(bodyNo, typeNo), input.exceptionScopes)

        val zeros  = divByZeroNodes(listOf(guardExpr), contBody, input, repos)
        return listOf<SymbolicTree>(SymbolicNode(resThen, info = InfoIfThen(guardExpr)), SymbolicNode(resElse, info = InfoIfElse(guardExpr))) + zeros
    }
}

object AEScopeSkip : Rule(Modality(
    SeqStmt(ScopeMarker, StmtAbstractVar("CONT")),
    AbstractAbstractVar("TYPE"))) {

    override fun transform(cond: MatchCondition, input : SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val pitype = cond.map[AbstractAbstractVar("TYPE")] as AbstractType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, pitype), input.exceptionScopes), info = InfoScopeClose())
        return listOf(res)
    }
}

object AESkip : Rule(Modality(
    SkipStmt,
    AbstractPost(FormulaAbstractVar("POST")))) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val target = cond.map[FormulaAbstractVar("POST")] as Formula
        val res = LogicNode(
            input.condition,
            UpdateOnFormula(input.update, target),
            info = InfoSkipEnd(target)
        )
        return listOf(res)
    }
}

object AESkipSkip : Rule(
    Modality(
    SeqStmt(SkipStmt, StmtAbstractVar("CONT")),
    AbstractAbstractVar("TYPE"))
) {

    override fun transform(cond: MatchCondition, input: SymbolicState): List<SymbolicTree> {
        val cont = cond.map[StmtAbstractVar("CONT")] as Stmt
        val type = cond.map[AbstractAbstractVar("TYPE")] as AbstractType
        val res = SymbolicNode(SymbolicState(input.condition, input.update, Modality(cont, type), input.exceptionScopes), info = InfoSkip())
        return listOf(res)
    }
}

fun extractUpdateFromForm(input : Formula) : UpdateElement{
    return when(input){
        is And-> ChainUpdate(extractUpdateFromForm(input.left), extractUpdateFromForm(input.right))
        is Or -> ChainUpdate(extractUpdateFromForm(input.left), extractUpdateFromForm(input.right))
        is Impl -> ChainUpdate(extractUpdateFromForm(input.left), extractUpdateFromForm(input.right))
        is Not -> extractUpdateFromForm(input.left)
        is UpdateOnFormula -> ChainUpdate(input.update, extractUpdateFromForm(input.target))
        is Predicate, is ImplementsForm, is Eq, is True, is False, is AbstractFormula -> EmptyUpdate
        else -> throw Exception("Unusual formula to extract updates from : $input")
    }
}

