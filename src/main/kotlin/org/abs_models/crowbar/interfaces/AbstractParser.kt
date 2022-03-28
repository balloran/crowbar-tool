package org.abs_models.crowbar.interfaces

import antlr.crowbar.gen.AbstractExecutionBaseVisitor
import antlr.crowbar.gen.AbstractExecutionLexer
import antlr.crowbar.gen.AbstractExecutionParser
import org.abs_models.crowbar.types.AbstractType
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

object AbstractParser : AbstractExecutionBaseVisitor<AbstractType>() {

    fun parse(annotation:String) {

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
            parser.entry().accept(this)
        } catch (e : Exception){
            throw Exception("Could not parse abstract execution specification $annotation: \n${e.message}\n{${e.cause}")
        }
    }
}