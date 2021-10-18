package org.abs_models.crowbar.investigator

object ModelParser {

    private var tokens: MutableList<Token> = mutableListOf()

    fun loadSMT(smtString: String) {
        tokens.clear()
        tokens.addAll(Tokenizer.tokenize(smtString))

        if (tokens[0].toString() == "sat")
            tokens.removeAt(0)
    }

    fun parseModel(): List<ModelFunction> {
        consume(LParen())

        // the model keyword is apparently optional 
        if (tokens[0].toString() == "model")
            consume()

        val model = mutableListOf<ModelFunction>()

        while (tokens[0] is LParen) {
            if (tokens[1].toString() == "define-fun")
                model.add(parseDefinition())
            else
                ignore()
        }

        consume(RParen())

        return model
    }

    fun parseArrayValues(): List<MvArray> {
        consume(LParen())

        if (checkForSMTError())
            return listOf()

        val model = mutableListOf<MvArray>()

        while (tokens[0] is LParen) {
            consume()
            ignore()
            model.add(parseArrayExp())
            consume(RParen())
        }

        consume(RParen())

        return model
    }

    fun parseScalarValues(): List<ModelValue> {
        consume(LParen())

        if (checkForSMTError())
            return listOf()

        val values = mutableListOf<ModelValue>()

        while (tokens[0] is LParen) {
            consume()
            ignore()
            values.add(parseScalarValue())
            consume(RParen())
        }

        consume(RParen())

        return values
    }

    private fun parseDefinition(): ModelFunction {
        consume(LParen())
        consume(Identifier("define-fun"))

        val name = tokens[0].toString()
        consume()

        val args = parseArguments()
        val type = parseType()

        // Functions are annoying to parse & evaluate, so we won't
        // Heap definitions of Array type can get complex once counterexamples reach a certain size
        // So we will only parse simple constant definitions here
        // Parsing of heaps and relevant functions is handled elsewhere
        val value: ModelValue = if (args.isEmpty() && (type == Type.INT || type == Type.COMPLEX || type == Type.FUTURE))
            parseValue(type)
        else {
            ignore()
            UnknownValue
        }

        consume(RParen())

        return if (args.isEmpty())
            ModelConstant(name, type, value)
        else
            ModelFunction(name, type, args, value)
    }

    private fun parseArguments(): List<ModelTypedVariable> {
        val args = mutableListOf<ModelTypedVariable>()
        consume(LParen())

        while (tokens[0] is LParen)
            args.add(parseTypedVariable())

        consume(RParen())
        return args
    }

    private fun parseTypedVariable(): ModelTypedVariable {
        consume(LParen())
        val name = tokens[0].toString()
        consume()
        val type = parseType()
        consume(RParen())

        return ModelTypedVariable(type, name)
    }

    private fun parseType(): Type {
        when (tokens[0]) {
            is LParen -> {
                consume()
                consume(Identifier("Array"))
                parseType()
                parseType()
                consume(RParen())
                return Type.ARRAY
            }
            is Identifier -> {
                val typeid = tokens[0].spelling
                consume()
                return when (typeid) {
                    "Int" -> Type.INT
                    "Bool" -> Type.BOOL
                    "String" -> Type.STRING
                    "ABS.StdLib.Fut" -> Type.FUTURE
                    "ABS.StdLib.String" -> Type.STRING
                    else -> Type.COMPLEX
                }
            }
            else -> throw Exception("Expected scalar or array type but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
        }
    }

    private fun parseValue(expectedType: Type): ModelValue {
        return when (expectedType) {
            Type.INT -> parseIntExp()
            Type.FLOAT -> parseFloatExp()
            Type.STRING -> parseStringExp()
            Type.COMPLEX -> parseComplexTypeExp()
            Type.ARRAY -> parseArrayExp()
            Type.BOOL -> parseBoolExp()
            Type.FUTURE -> parseFutureTypeExp()
            Type.UNKNOWN -> throw Exception("Can't parse value of unknown type")
        }
    }

    private fun parseScalarValue(): ModelValue {
        println(tokens[0])
        return when (tokens[0]) {
            is ConcreteIntValue -> parseValue(Type.INT)
            is ConcreteFloatValue -> parseValue(Type.FLOAT)
            is StringLiteral -> parseValue(Type.STRING)
            is Identifier -> {
                val id = tokens[0].spelling
                when {
                    id == "true" || id ==  "false" -> parseValue(Type.BOOL)
                    id matches Regex("^ABS\\.StdLib\\.String!val!.*") -> parseValue(Type.STRING)
                    else -> parseValue(Type.COMPLEX)
                }
            }
            is LParen -> {
                when (tokens[1].toString()) {
                    "-" -> parseValue(Type.INT)
                    "/" -> parseValue(Type.FLOAT)
                    else -> parseValue(Type.COMPLEX)
                }
            }
            else -> throw Exception("Cannot guess type of value at ${tokens.joinToString(" ")}")
        }
    }

    private fun parseIntExp(): MvInteger {
        when (tokens[0]) {
            is ConcreteIntValue -> {
                val value = (tokens[0] as ConcreteIntValue).value
                consume()
                return MvInteger(value)
            }
            is LParen -> {
                consume()
                val value: Int

                when (tokens[0].toString()) {
                    "-" -> {
                        consume()
                        value = - parseIntExp().value
                    }
                    else -> throw Exception("Expected integer expression function but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
                }
                consume(RParen())
                return MvInteger(value)
            }
            else -> throw Exception("Expected concrete integer value but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
        }
    }

    private fun parseFloatExp(): MvFloat {
        when (tokens[0]) {
            is ConcreteFloatValue -> {
                val value = (tokens[0] as ConcreteFloatValue).value
                consume()
                return MvFloat(value)
            }
            is ConcreteIntValue -> {
                val value = (tokens[0] as ConcreteIntValue).value
                consume()
                return MvFloat(value.toDouble())
            }
            is LParen -> {
                consume()

                val value: Double = when (tokens[0].toString()) {
                    "-" -> {
                        consume()
                        - parseFloatExp().value
                    }
                    "/" -> {
                        consume()
                        val a = parseFloatExp().value
                        val b = parseFloatExp().value
                        a / b
                    }
                    else -> throw Exception("Expected float expression function but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
                }
                consume(RParen())
                return MvFloat(value)
            }
            else -> throw Exception("Expected concrete float value but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
        }
    }

    private fun parseStringExp(): MvString {
        return when (tokens[0]) {
            is StringLiteral -> {
                val value = (tokens[0] as StringLiteral).value
                consume()
                MvString(value)
            }
            is Identifier -> {
                if (tokens[0].spelling.startsWith("ABS.StdLib.String!val!")) {
                    val id = tokens[0].spelling.removePrefix("ABS.StdLib.String!val!")
                    consume()
                    MvString("stringLiteral#$id")
                } else
                    throw Exception("Expected string variable but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
            }
            else -> throw Exception("Expected string value but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
        }
    }

    private fun parseArrayExp(defs: Map<String, List<Token>> = mapOf()): MvArray {
        val array: MvArray

        // If we find a previously declared identifier, pretend we read the defined
        // replacement token sequence instead. Hacky, I know.
        if (tokens[0] is Identifier && defs.containsKey(tokens[0].toString())) {
            val id = tokens[0].toString()
            consume()
            tokens = (defs[id]!! + tokens).toMutableList()
        }

        consume(LParen())

        when (tokens[0]) {
            is LParen -> array = parseConstArray()
            Identifier("let") -> {
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
            }
            Identifier("store") -> {
                consume()
                array = parseArrayExp(defs)
                val elemType = array.elemType
                val index = parseIntExp().value
                val value = parseValue(elemType)
                array.map[index] = value
            }
            Identifier("lambda") -> {
                // This is fragile - I'm hoping lambdas are only generated for very simple boolean array expressions
                // At this point we only support lambdas that result in an all-false array with a single true value at a given index
                consume()
                val args = parseArguments()

                if (args.size != 1)
                    throw Exception("Lambda with more than one argument in SMT array expression - unsupported")

                consume(LParen())
                consume(Identifier("="))
                consume(Identifier(args[0].name))

                if (tokens[0] !is ConcreteIntValue)
                    throw Exception("Unsupported complex lambda in SMT array expression")

                val index = (tokens[0] as ConcreteIntValue).value
                consume()
                consume(RParen())
                array = MvArray(Type.BOOL, MvBoolean(false))
                array.map[index] = MvBoolean(true)
            }
            else -> throw Exception("Unexpected token \"${tokens[0]}\" in array expression")
        }

        consume(RParen())
        return array
    }

    private fun parseComplexTypeExp(): MvDataType {
        when (tokens[0]) {
            // Simple types without parameters
            is Identifier -> {
                val value = (tokens[0] as Identifier).spelling
                consume()
                return MvDataType(value)
            }
            // Types with parameters
            is LParen -> {
                consume()

                if (tokens[0] !is Identifier)
                    throw Exception("Expected data type constructor but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
                val typeConstructor = (tokens[0] as Identifier).spelling
                consume()

                val params = mutableListOf<ModelValue>()
                while (tokens[0] !is RParen) {
                    params.add(parseScalarValue())
                }
                consume(RParen())

                return MvDataType(typeConstructor, params)
            }
            else -> throw Exception("Expected data type value but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
        }
    }

    private fun parseFutureTypeExp(): MvFuture {
        if (tokens[0] !is Identifier)
            throw Exception("Expected future expression but got '${tokens[0]}' at ${tokens.joinToString(" ")}")

        val spelling = tokens[0].spelling
        consume()

        return MvFuture(spelling)
    }

    private fun parseBoolExp(): MvBoolean {
        // Simple types without parameters
        if (tokens[0].toString() == "true" || tokens[0].toString() == "false") {
            val value = (tokens[0] as Identifier).spelling == "true"
            consume()
            return MvBoolean(value)
        } else
            throw Exception("Expected boolean expression but got '${tokens[0]}' at ${tokens.joinToString(" ")}")
    }

    private fun parseConstArray(): MvArray {
        consume(LParen())
        consume(Identifier("as"))
        consume(Identifier("const"))
        consume(LParen())
        consume(Identifier("Array"))
        parseType()
        val valType = parseType()
        consume(RParen())
        consume(RParen())
        val value = parseValue(valType)
        return MvArray(valType, value)
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

open class ModelFunction(val name: String, val type: Type, val args: List<ModelTypedVariable>, val value: ModelValue) {
    override fun toString() = "Function '$name(${args.joinToString(", ")})' of type '$type' set to '$value'"
}

class ModelConstant(name: String, type: Type, value: ModelValue) : ModelFunction(name, type, listOf(), value) {
    override fun toString() = "Constant '$name' of type '$type' set to '$value'"
}

data class ModelTypedVariable(val type: Type, val name: String) {
    override fun toString() = "$name: $type"
}

interface ModelValue

object UnknownValue : ModelValue {
    override fun toString() = "UNPARSED VALUE"
}

data class MvArray(val elemType: Type, val defaultValue: ModelValue, val map: MutableMap<Int, ModelValue> = mutableMapOf()) : ModelValue {
    fun getValue(index: Int) = if (map.contains(index)) map[index]!! else defaultValue

    override fun toString(): String {
        val entries = mutableListOf("default: $defaultValue")
        map.forEach {
            entries.add("${it.key}: ${it.value}")
        }

        return "[${entries.joinToString(", ")}]"
    }
}

data class MvInteger(val value: Int) : ModelValue {
    override fun toString() = value.toString()
}

data class MvFloat(val value: Double) : ModelValue {
    override fun toString() = value.toString()
}

data class MvBoolean(val value: Boolean) : ModelValue {
    override fun toString() = value.toString()
}

data class MvString(val value: String) : ModelValue {
    override fun toString() = "\"$value\""
}

data class MvDataType(val value: String, val params: List<ModelValue> = listOf()) : ModelValue {
    override fun toString(): String {
        return if (params.isEmpty())
            stripModulePrefix(value)
        else
            "${stripModulePrefix(value)}(${params.joinToString(", ")})"
    }
}

data class MvFuture(val id: String) : ModelValue {
    override fun toString() = id
}

enum class Type {
    INT, BOOL, STRING, FLOAT, ARRAY, COMPLEX, FUTURE, UNKNOWN
}
