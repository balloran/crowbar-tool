package org.abs_models.crowbar.investigator

object Tokenizer {

    private val whitespace = Regex("\\s")
    private val numeric = Regex("(\\-)?\\d+")
    private val allowedId = Regex("[^\\s\"\'\\)\\(\\]\\[]")
    private val allowedStringLit = Regex("[^\"]")

    fun tokenize(code: String): List<Token> {

        val tokens = mutableListOf<Token>()
        var i = 0

        // Extract single token until end of input reached
        while (i < code.length) {

            val char = code[i].toString()
            i += 1

            when {
                char == "(" -> tokens.add(LParen())
                char == ")" -> tokens.add(RParen())
                char == "\"" -> {
                    var stringLit = ""
                    while (i < code.length && allowedStringLit matches code[i].toString()) {
                        stringLit += code[i]
                        i += 1
                    }
                    i += 1 // Skip closing quote
                    tokens.add(StringLiteral(stringLit))
                }
                char matches whitespace -> {}
                char matches allowedId -> {
                    var identifier = char
                    while (i < code.length && allowedId matches code[i].toString()) {
                        identifier += code[i]
                        i += 1
                    }

                    if (numeric matches identifier)
                        // The solver occasionally comes up with huge integer literals
                        // parsing them as ints fails, so we will parse as long and
                        // cut to int size. This might cause some incorrect counterexamples.
                        tokens.add(ConcreteValue(identifier.toLong().toInt()))
                    else
                        tokens.add(Identifier(identifier))
                }
                else -> throw Exception("Unknown character at position $i: '$char'")
            }
        }

        return tokens
    }
}

abstract class Token(val spelling: String) {
    override fun toString() = spelling

    override fun equals(other: Any?): Boolean {
        return if (other != null && other is Token)
            toString() == other.toString()
        else
            false
    }

    override fun hashCode() = toString().hashCode()
}

class LParen() : Token("(")
class RParen() : Token(")")
class StringLiteral(content: String) : Token("\"$content\"")
class Identifier(spelling: String) : Token(spelling)
class ConcreteValue(val value: Int) : Token(value.toString())
