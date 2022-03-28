package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.AssignStmt
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.interfaces.translateExpression
import org.abs_models.crowbar.interfaces.translateStatement
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.UnknownType
import kotlin.system.exitProcess


/**
 * DeductType for abstract Execution, lots of things to do
 */

interface AbstractExecType : DeductType{
    companion object : AbstractExecType

    /**
     * Return the emptiest possible node just for programming purpose, might change/disappear in the future.
     */

    fun totallyEmptyNode() : SymbolicNode{
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(SkipStmt, EmptyAbstractExecType), listOf()))
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

        extractGlobalAbstractExecTypeSpec(model)

        //output("${model.mainBlock}")
        val v = appendStmt(translateStatement(model.mainBlock, emptyMap()), SkipStmt)
        //output("$v")
        return SymbolicNode(SymbolicState(True, EmptyUpdate, Modality(v, PostInvariantPair(True, True)), listOf()), emptyList())
    }

    fun extractGlobalAbstractExecTypeSpec(model: Model): Formula{

        var globalSpec = extractGlobalSpec(model.mainBlock)

        return globalSpec
    }


    override fun extractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
        return totallyEmptyNode()
    }

    fun extractAbstractNode(): SymbolicNode{
        return totallyEmptyNode()
    }
}

object EmptyAbstractExecType : AbstractExecType{

}