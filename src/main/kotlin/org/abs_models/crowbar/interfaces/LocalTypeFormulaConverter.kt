package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.LocalSessionBaseVisitor
import antlr.crowbar.gen.LocalSessionParser.And_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Binary_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Boolean_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Field_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Function_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Not_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Or_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Predicate_type_formulaContext
import org.abs_models.crowbar.data.And
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.LogicElement
import org.abs_models.crowbar.data.Not
import org.abs_models.crowbar.data.Or
import org.abs_models.crowbar.data.Predicate
import org.abs_models.crowbar.data.Term

object LocalTypeFormulaConverter : LocalSessionBaseVisitor<LogicElement>() {

    override fun visitOr_type_formula(ctx: Or_type_formulaContext): Formula {
        val left = ctx.formula(0).accept(this) as Formula
        val right = ctx.formula(1).accept(this) as Formula
        return Or(left, right)
    }

    override fun visitBoolean_type_formula(ctx: Boolean_type_formulaContext): Formula {
        val term = ctx.term().accept(this) as Term
        return Predicate("=", listOf(term, Function("1")))
    }

    override fun visitNot_type_formula(ctx: Not_type_formulaContext): Formula {
        return Not(ctx.formula().accept(this) as Formula)
    }

    override fun visitPredicate_type_formula(ctx: Predicate_type_formulaContext): Formula {
        val args = ctx.termlist().term().map { it.accept(this) as Term }
        return Predicate(ctx.STRING().getText(), args)
    }

    override fun visitAnd_type_formula(ctx: And_type_formulaContext): Formula {
        val left = ctx.formula(0).accept(this) as Formula
        val right = ctx.formula(1).accept(this) as Formula
        return And(left, right)
    }

    override fun visitFunction_type_term(ctx: Function_type_termContext): Term {
        val name = ctx.STRING().getText()
        val args = ctx.termlist().term().map { it.accept(this) as Term }
        return Function(name, args)
    }

    override fun visitBinary_type_term(ctx: Binary_type_termContext): Term {
        val op = ctx.STRING().getText()
        val left = ctx.term(0).accept(this) as Term
        val right = ctx.term(1).accept(this) as Term
        return Function(op, listOf(left, right))
    }

    override fun visitField_type_term(ctx: Field_type_termContext): Term {
        return Field(ctx.STRING().getText(), "<UNKNOWN>")
    }
}
