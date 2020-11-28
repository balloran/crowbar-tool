package org.abs_models.crowbar.investigator

object ModelParser {

    var tokens: MutableList<Token> = mutableListOf()

    fun loadSMT(smtString: String) {
        tokens.clear()
        tokens.addAll(Tokenizer.tokenize(smtString))

        if (tokens[0].toString() == "sat")
            tokens.removeAt(0)
    }

    fun parseModel(): List<Function> {
        consume(LParen())
        consume(Identifier("model"))

        val model = mutableListOf<Function>()

        while (tokens[0] is LParen)
            model.add(parseDefinition())

        consume(RParen())

        return model
    }

    fun parseArrayValues(): List<Array> {
        consume(LParen())

        if (checkForSMTError())
            return listOf()

        val model = mutableListOf<Array>()

        while (tokens[0] is LParen) {
            consume()
            ignore()
            model.add(parseArrayExp())
            consume(RParen())
        }

        consume(RParen())

        return model
    }

    fun parseIntegerValues(): List<Int> {
        consume(LParen())

        if (checkForSMTError())
            return listOf()

        val values = mutableListOf<Int>()

        while (tokens[0] is LParen) {
            consume()
            ignore()
            values.add(parseIntExp())
            consume(RParen())
        }

        consume(RParen())

        return values
    }

    private fun parseDefinition(): Function {
        consume(LParen())
        consume(Identifier("define-fun")) // Is this always true?

        val name = tokens[0].toString()
        consume()

        val args = parseArguments()
        val type = parseType()

        val value: Value

        // Functions are annoying to parse & evaluate, so we won't
        // Heap definitions of Array type can get complex once counterexamples reach a certain size
        // So we will only parse simple integer constant definitions here
        // Parsing of heaps and relevant functions is handled elsewhere
        if (args.size == 0 && type == Type.INT)
            value = parseValue(type)
        else {
            ignore()
            value = UnknownValue
        }

        consume(RParen())

        return if (args.size == 0)
            Constant(name, type, value)
        else
            Function(name, type, args, value)
    }

    private fun parseArguments(): List<TypedVariable> {
        val args = mutableListOf<TypedVariable>()
        consume(LParen())

        while (tokens[0] is LParen)
            args.add(parseTypedVariable())

        consume(RParen())
        return args
    }

    private fun parseTypedVariable(): TypedVariable {
        consume(LParen())
        val name = tokens[0].toString()
        consume()
        val type = parseType()
        consume(RParen())

        return TypedVariable(type, name)
    }

    private fun parseType(): Type {
        if (tokens[0] is LParen) {
            consume()
            consume(Identifier("Array"))
            consume(Identifier("Int"))
            consume(Identifier("Int"))
            consume(RParen())
            return Type.ARRAY
        } else {
            consume(Identifier("Int"))
            return Type.INT
        }
    }

    private fun parseValue(expectedType: Type): Value {
        if (expectedType == Type.INT) {
            return Integer(parseIntExp())
        } else
            return parseArrayExp()
    }

    private fun parseIntExp(): Int {
        if (tokens[0] is ConcreteValue) {
            val value = (tokens[0] as ConcreteValue).value
            consume()
            return value
        } else if (tokens[0] is LParen) {
            consume()
            val value: Int

            when (tokens[0].toString()) {
                "-" -> {
                    consume()
                    value = - parseIntExp()
                }
                else -> throw Exception("Expected integer expression function but got '${tokens[0]}'' at ${tokens.joinToString(" ")}")
            }
            consume(RParen())
            return value
        } else
            throw Exception("Expected concrete integer value but got '${tokens[0]}'' at ${tokens.joinToString(" ")}")
    }

    private fun parseArrayExp(defs: Map<String, List<Token>> = mapOf()): Array {
        val array: Array

        // If we find a previously declared identifier, pretend we read the defined
        // replacement token sequence instead. Hacky, I know.
        if (tokens[0] is Identifier && defs.containsKey(tokens[0].toString())) {
            val id = tokens[0].toString()
            consume()
            tokens = (defs[id]!! + tokens).toMutableList()
        }

        consume(LParen())

        if (tokens[0] is LParen)
            array = parseConstArray()
        else if (tokens[0] == Identifier("let")) {
            val newDefs = defs.toMutableMap()
            consume()
            consume(LParen())
            // Parse 'macro' definitions
            while (tokens[0] is LParen) {
                consume()
                val id = (tokens[0] as Identifier).toString()
                consume()
                // Save token sequence for replacements
                newDefs[id] = extractSubexpression()
                consume(RParen())
            }

            consume(RParen())
            array = parseArrayExp(newDefs)
        } else if (tokens[0] == Identifier("store")) {
            consume()
            array = parseArrayExp(defs)
            val index = parseIntExp()
            val value = parseIntExp()
            array.map.put(index, value)
        } else
            throw Exception("Unexpected token \"${tokens[0]}\" in array expression")

        consume(RParen())
        return array
    }

    private fun parseConstArray(): Array {
        consume(LParen())
        consume(Identifier("as"))
        consume(Identifier("const"))
        consume(LParen())
        consume(Identifier("Array"))
        consume(Identifier("Int"))
        consume(Identifier("Int"))
        consume(RParen())
        consume(RParen())
        val value = parseIntExp()
        return Array(value)
    }

    private fun checkForSMTError(): Boolean {
        return if (tokens[0] == Identifier("error")) {
            consume()
            val eMsg = (tokens[0] as StringLiteral).toString()
            consume()
            consume(RParen())
            System.err.println("SMT solver error: $eMsg")
            true
        } else
            false
    }

    // Consume a subexpression without doing anything
    private fun ignore() {
        var layer = if (tokens[0] is LParen) 1 else 0
        consume()

        while (layer > 0) {
            if (tokens[0] is LParen)
                layer++
            else if (tokens[0] is RParen)
                layer--

            consume()
        }
    }

    // Consume a subexpression and return it as a list of tokens
    private fun extractSubexpression(): List<Token> {
        val extracted = mutableListOf<Token>()

        var layer = if (tokens[0] is LParen) 1 else 0
        extracted.add(tokens[0])
        consume()

        while (layer > 0) {
            if (tokens[0] is LParen)
                layer++
            else if (tokens[0] is RParen)
                layer--

            extracted.add(tokens[0])
            consume()
        }

        return extracted
    }

    private fun consume(expected: Token? = null) {
        if (tokens.size == 0)
            throw Exception("Expected token but got end of input")

        val got = tokens.removeAt(0)

        if (expected != null && got != expected)
            throw Exception("Expected '$expected' but got '$got' at ${tokens.joinToString(" ")}")
    }
}

open class Function(val name: String, val type: Type, val args: List<TypedVariable>, val value: Value) {
    override fun toString() = "Function '$name(${args.joinToString(", ")})' of type '$type' set to '$value'"
}

class Constant(name: String, type: Type, value: Value) : Function(name, type, listOf(), value) {
    override fun toString() = "Constant '$name' of type '$type' set to '$value'"
}

data class TypedVariable(val type: Type, val name: String) {
    override fun toString() = "$name: $type"
}

interface Value

object UnknownValue : Value {
    override fun toString() = "UNPARSED VALUE"
}

class Array(val defaultValue: Int, val map: MutableMap<Int, Int> = mutableMapOf()) : Value {
    fun getValue(index: Int) = if (map.contains(index)) map[index]!! else defaultValue

    override fun toString(): String {
        val entries = mutableListOf("default: $defaultValue")
        map.forEach {
            entries.add("${it.key}: ${it.value}")
        }

        return "[${entries.joinToString(", ")}]"
    }
}

class Integer(val value: Int) : Value {
    override fun toString() = value.toString()
}

enum class Type() {
    INT, ARRAY, UNKNOWN
}
