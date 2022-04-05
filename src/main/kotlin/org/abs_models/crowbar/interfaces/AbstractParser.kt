package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.AbstractExecutionBaseVisitor
import antlr.crowbar.gen.AbstractExecutionLexer
import antlr.crowbar.gen.AbstractExecutionParser
import org.abs_models.crowbar.data.*
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

object AbstractParser : AbstractExecutionBaseVisitor<AESpec>() {

    private var termConverter: AbstractTermParser = AbstractTermParser()

    fun parse(annotation:String) : AESpec{

        val stream = CharStreams.fromString(annotation)

        //output(stream.toString())

        val lexer = AbstractExecutionLexer(stream)
        //lexer.removeErrorListeners()
        //lexer.addErrorListener(ThrowingErrorListener)

        val tokens = CommonTokenStream(lexer)
        val parser = AbstractExecutionParser(tokens)
        //parser.removeErrorListeners()
        //parser.addErrorListener(ThrowingErrorListener)

        try {
            return parser.entry().accept(this)
        } catch (e : Exception){
            throw Exception("Could not parse abstract execution specification $annotation: \n${e.message}\n{${e.cause}")
        }
    }

    override fun visitLocation_declaration(ctx: AbstractExecutionParser.Location_declarationContext?): AESpec {
        return AELocDec(ctx?.ids_loc()!!.accept(termConverter) as List<AELoc>)
    }

    override fun visitFormula_declaration(ctx: AbstractExecutionParser.Formula_declarationContext?): AESpec {
        return AEForDec(ctx?.formula_dec()!!.accept(termConverter) as List<AEPhiDec>)
    }

    override fun visitDisjoint_constraint(ctx: AbstractExecutionParser.Disjoint_constraintContext?): AESpec {
        return AEDis(ctx?.ids_loc()!!.accept(termConverter) as List<AELoc>)
    }

    override fun visitMutex_constraint(ctx: AbstractExecutionParser.Mutex_constraintContext?): AESpec {
        return AEMut(ctx?.formula_list()!!.accept(termConverter) as List<AEPhi>)
    }

    override fun visitStatement_local(ctx: AbstractExecutionParser.Statement_localContext?): AESpec {
        return AEStatement(ctx?.aps_name()!!.text)
    }

    override fun visitExpression_local(ctx: AbstractExecutionParser.Expression_localContext?): AESpec {
        return AEExpression(ctx?.ape_name()!!.text)
    }

    override fun visitAssignable_local(ctx: AbstractExecutionParser.Assignable_localContext?): AESpec {
        return AEAssignable(ctx?.ass_list()!!.accept(termConverter) as List<AELoc>)
    }

    override fun visitAccessible_local(ctx: AbstractExecutionParser.Accessible_localContext?): AESpec {
        return AEAccessible(ctx?.ids_loc()!!.accept(termConverter) as List<AELoc>)
    }

    override fun visitReturn_local(ctx: AbstractExecutionParser.Return_localContext?): AESpec {
        return AERetBehavior(ctx?.formula()!!.accept(termConverter) as AEPhi)
    }
}

class AbstractTermParser : AbstractExecutionBaseVisitor<List<AETerm>>(){

    override fun visitFormula_dec(ctx: AbstractExecutionParser.Formula_decContext?): List<AETerm> {
        return ctx?.simple_dec()!!.map { it.accept(this) }.flatten()
    }

    override fun visitSimple_dec(ctx: AbstractExecutionParser.Simple_decContext?): List<AETerm> {
        return listOf(AEPhiDec(ctx?.id_formula()!!.text))
    }

    override fun visitFormula_list(ctx: AbstractExecutionParser.Formula_listContext?): List<AETerm> {
        return ctx?.formula()!!.map { it.accept(this) }.flatten()
    }

    override fun visitFormula(ctx: AbstractExecutionParser.FormulaContext?): List<AETerm> {
        if(ctx?.TRUE() != null){
            return listOf(AETrue)
        }
        else if(ctx?.FALSE() != null){
            return listOf(AEFalse)
        }
        else{
            return listOf(AEInstantiatedPhi(ctx?.id_formula()!!.text, ctx.id_loc().text))
        }
    }

    override fun visitIds_loc(ctx: AbstractExecutionParser.Ids_locContext?): List<AETerm> {
        return ctx?.id_loc()!!.map { it.accept(this) }.flatten()
    }

    override fun visitId_loc(ctx: AbstractExecutionParser.Id_locContext?): List<AETerm> {
        if(ctx?.EVERYTHING() != null){
            return listOf(AEEverything)
        }
        else if(ctx?.NOTHING() != null){
            return listOf(AENothing)
        }
        else{
            return listOf(AEInstantiatedLoc(ctx?.loc_name()!!.text))
        }
    }

    override fun visitAss_list(ctx: AbstractExecutionParser.Ass_listContext?): List<AETerm> {
        return ctx?.assignable()!!.map { it.accept(this) }.flatten()
    }

    override fun visitSimple_assignable(ctx: AbstractExecutionParser.Simple_assignableContext?): List<AETerm> {
        return listOf(AEInstantiatedLoc(ctx?.id_loc()!!.text))
    }

    override fun visitHasTo_assignable(ctx: AbstractExecutionParser.HasTo_assignableContext?): List<AETerm> {
        return listOf(AEHasToLoc(ctx?.id_loc()!!.accept(this)[0] as AELoc))
    }
}