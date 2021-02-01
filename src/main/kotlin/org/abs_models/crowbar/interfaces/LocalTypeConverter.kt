package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.LocalSessionBaseVisitor
import antlr.crowbar.gen.LocalSessionParser.Call_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Get_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Nested_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Or_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Put_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Rep_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Seq_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Skip_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Susp_local_typeContext
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.LTCall
import org.abs_models.crowbar.data.LTGet
import org.abs_models.crowbar.data.LTNest
import org.abs_models.crowbar.data.LTOpt
import org.abs_models.crowbar.data.LTPut
import org.abs_models.crowbar.data.LTRep
import org.abs_models.crowbar.data.LTSeq
import org.abs_models.crowbar.data.LTSkip
import org.abs_models.crowbar.data.LTSusp
import org.abs_models.crowbar.data.LocalType
import org.abs_models.crowbar.data.Term

object LocalTypeConverter : LocalSessionBaseVisitor<LocalType>() {

    override fun visitCall_local_type(ctx: Call_local_typeContext): LocalType {
        val role = ctx.role().STRING().getText()
        val method = ctx.STRING().getText()
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Formula
        return LTCall(role, method, formula)
    }

    override fun visitRep_local_type(ctx: Rep_local_typeContext): LocalType {
        val inner = ctx.local().accept(this)
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Formula
        return LTRep(inner, formula)
    }

    override fun visitPut_local_type(ctx: Put_local_typeContext): LocalType {
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Formula
        return LTPut(formula)
    }

    override fun visitSkip_local_type(ctx: Skip_local_typeContext): LocalType {
        return LTSkip()
    }

    override fun visitNested_local_type(ctx: Nested_local_typeContext): LocalType {
        return LTNest(ctx.local().accept(this))
    }

    override fun visitOr_local_type(ctx: Or_local_typeContext): LocalType {
        val left = ctx.local(0).accept(this)
        val right = ctx.local(1).accept(this)
        return LTOpt(left, right)
    }

    override fun visitGet_local_type(ctx: Get_local_typeContext): LocalType {
        val term = ctx.term().accept(LocalTypeFormulaConverter) as Term
        return LTGet(term)
    }

    override fun visitSusp_local_type(ctx: Susp_local_typeContext): LocalType {
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Formula
        return LTSusp(formula)
    }

    override fun visitSeq_local_type(ctx: Seq_local_typeContext): LocalType {
        val first = ctx.local(0).accept(this)
        val second = ctx.local(1).accept(this)
        return LTSeq(first, second)
    }
}
