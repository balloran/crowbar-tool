package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.AbstractExecutionBaseVisitor
import antlr.crowbar.gen.AbstractExecutionLexer
import antlr.crowbar.gen.AbstractExecutionParser
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.types.AbstractExecType
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType
import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer

object AbstractExecParser : AbstractExecutionBaseVisitor<AbstractExecType>() {

    fun parse(annotation:String) : AbstractExecType{

        val stream = CharStreams.fromString(annotation)

        output(stream.toString())

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
            throw Exception("Could not parse abstract execution specification $annotation: \n${e.message}")
        }
    }
}