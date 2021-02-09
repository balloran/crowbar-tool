package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.LocalSessionBaseVisitor
import antlr.crowbar.gen.LocalSessionLexer
import antlr.crowbar.gen.LocalSessionParser
import antlr.crowbar.gen.LocalSessionParser.And_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Binary_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Boolean_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Call_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Constant_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Field_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Function_type_termContext
import antlr.crowbar.gen.LocalSessionParser.Get_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Nested_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Not_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Or_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Or_type_formulaContext
import antlr.crowbar.gen.LocalSessionParser.Put_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Rep_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Seq_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Skip_local_typeContext
import antlr.crowbar.gen.LocalSessionParser.Susp_local_typeContext
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
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
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.ReturnVar
import org.abs_models.crowbar.data.SExpr
import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer

object LocalTypeParser : LocalSessionBaseVisitor<LocalType>() {
    fun parse(localTypeExp: String): LocalType {
        val stream = CharStreams.fromString(localTypeExp)

        val lexer = LocalSessionLexer(stream)
        lexer.removeErrorListeners()
        lexer.addErrorListener(ThrowingErrorListener)

        val tokens = CommonTokenStream(lexer)
        val parser = LocalSessionParser(tokens)
        parser.removeErrorListeners()
        parser.addErrorListener(ThrowingErrorListener)

        try {
            return parser.local().accept(this)
        } catch (e: LocalTypeParsingException) {
            throw Exception("Could not parse local type expression '$localTypeExp':\n${e.message}")
        }
    }

    override fun visitCall_local_type(ctx: Call_local_typeContext): LocalType {
        val role = ctx.role().STRING().getText()
        val method = ctx.STRING().getText()
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Expr
        return LTCall(role, method, formula)
    }

    override fun visitRep_local_type(ctx: Rep_local_typeContext): LocalType {
        val inner = ctx.local().accept(this)
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Expr
        return LTRep(inner, formula)
    }

    override fun visitPut_local_type(ctx: Put_local_typeContext): LocalType {
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Expr
        return LTPut(formula)
    }

    override fun visitSkip_local_type(ctx: Skip_local_typeContext): LocalType {
        return LTSkip
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
        val term = ctx.term().accept(LocalTypeFormulaConverter) as Expr
        return LTGet(term)
    }

    override fun visitSusp_local_type(ctx: Susp_local_typeContext): LocalType {
        val formula = ctx.formula().accept(LocalTypeFormulaConverter) as Expr
        return LTSusp(formula)
    }

    override fun visitSeq_local_type(ctx: Seq_local_typeContext): LocalType {
        val first = ctx.local(0).accept(this)
        val second = ctx.local(1).accept(this)
        return LTSeq(first, second)
    }
}

// Sub-converter for terms and formulas in local type expressions
object LocalTypeFormulaConverter : LocalSessionBaseVisitor<Expr>() {

    override fun visitOr_type_formula(ctx: Or_type_formulaContext): SExpr {
        val left = ctx.formula(0).accept(this) as Expr
        val right = ctx.formula(1).accept(this) as Expr
        return SExpr("||", listOf(left, right))
    }

    override fun visitBoolean_type_formula(ctx: Boolean_type_formulaContext): Expr {
        val term = ctx.term().accept(this) as Expr
        return SExpr("=", listOf(term, Const("true")))
    }

    override fun visitNot_type_formula(ctx: Not_type_formulaContext): Expr {
        return SExpr("!", listOf(ctx.formula().accept(this) as Expr))
    }

    override fun visitAnd_type_formula(ctx: And_type_formulaContext): Expr {
        val left = ctx.formula(0).accept(this) as Expr
        val right = ctx.formula(1).accept(this) as Expr
        return SExpr("&&", listOf(left, right))
    }

    override fun visitFunction_type_term(ctx: Function_type_termContext): Expr {
        val name = ctx.STRING().getText()
        val args = ctx.termlist().term().map { it.accept(this) as Expr }
        return SExpr(name, args)
    }

    override fun visitBinary_type_term(ctx: Binary_type_termContext): Expr {
        val op = ctx.binop().getText()
        val left = ctx.term(0).accept(this) as Expr
        val right = ctx.term(1).accept(this) as Expr
        return SExpr(op, listOf(left, right))
    }

    override fun visitField_type_term(ctx: Field_type_termContext): Expr {
        return Field(ctx.STRING().getText() + "_f", "<UNKNOWN>")
    }

    override fun visitConstant_type_term(ctx: Constant_type_termContext): Expr {
        val text = ctx.STRING().getText()
        return when (text) {
            "null" -> Const("0")
            "this" -> Const("1")
            "true" -> Const("true")
            "false" -> Const("false")
            "result" -> ReturnVar("<UNKNOWN>")
            else -> ProgVar(text, "<UNKNOWN>")
        }
    }
}

class LocalTypeParsingException(msg: String) : Exception(msg)

object ThrowingErrorListener : BaseErrorListener() {
    override fun syntaxError(recognizer: Recognizer<*, *>, offendingSymbol: Any?, line: Int, charPositionInLine: Int, msg: String, e: RecognitionException?) {
        throw LocalTypeParsingException("Error at position $line:$charPositionInLine $msg")
    }
}
