package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.Expr
import org.abs_models.crowbar.data.Field
import org.abs_models.crowbar.data.Formula
import org.abs_models.crowbar.data.Location
import org.abs_models.crowbar.data.ProgVar
import org.abs_models.crowbar.data.SExpr
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.tree.InfoAwaitUse
import org.abs_models.crowbar.tree.InfoBranch
import org.abs_models.crowbar.tree.InfoCallAssign
import org.abs_models.crowbar.tree.InfoClassPrecondition
import org.abs_models.crowbar.tree.InfoGetAssign
import org.abs_models.crowbar.tree.InfoIfElse
import org.abs_models.crowbar.tree.InfoIfThen
import org.abs_models.crowbar.tree.InfoInvariant
import org.abs_models.crowbar.tree.InfoLocAssign
import org.abs_models.crowbar.tree.InfoLoopInitial
import org.abs_models.crowbar.tree.InfoLoopPreserves
import org.abs_models.crowbar.tree.InfoLoopUse
import org.abs_models.crowbar.tree.InfoMethodPrecondition
import org.abs_models.crowbar.tree.InfoNullCheck
import org.abs_models.crowbar.tree.InfoObjAlloc
import org.abs_models.crowbar.tree.InfoReturn
import org.abs_models.crowbar.tree.InfoScopeClose
import org.abs_models.crowbar.tree.InfoSkip
import org.abs_models.crowbar.tree.InfoSkipEnd
import org.abs_models.crowbar.tree.InfoSyncCallAssign
import org.abs_models.crowbar.tree.NoInfo
import org.abs_models.crowbar.tree.NodeInfoVisitor
import org.abs_models.frontend.typechecker.Type

object NodeInfoRenderer : NodeInfoVisitor<String> {

    private var scopeLevel = 0
    private var objectCounter = 0
    private val objMap = mutableMapOf<String, String>()
    private val varDefs = mutableSetOf<Pair<String, Int>>()
    private val varTypes = mutableMapOf<String, String>()
    private val varRemaps = mutableMapOf<String, String>()
    private val usedFields = mutableSetOf<Field>()
    private var model = EmptyModel

    fun reset(newModel: Model) {
        model = newModel
        scopeLevel = 0
        objectCounter = 0
        objMap.clear()
        varDefs.clear()
        varTypes.clear()
        varRemaps.clear()
        usedFields.clear()
    }

    fun initAssignments(): String {
        val oldHeap = model.oldHeap
        // Do not render assignments for fields that do not change value from their declared values
        val initAssign = model.initState.filter { it.first is ProgVar || (it.first is Field && !oldHeap.contains(it)) }.map { renderModelAssignment(it.first, it.second) }
        val res = if (initAssign.isNotEmpty())
                "// Assume the following pre-state:\n${initAssign.joinToString("\n")}\n// End of setup\n"
            else
                ""
        return indent(res)
    }

    fun fieldDefs(): List<String> {
        // For more intuitive counterexamples, we initialize fields to their value in the state before method execution
        // The state in which the actual counterexample begins is initialized in the method-internal initial assignments
        val fields = model.oldHeap
        // Find fields not included in the model but included in the counterexample and initialize them with default value
        val missingFields = (usedFields - fields.map { it.first }.toSet()).map { Pair(it, getDefaultValueForType(it.concrType)) }

        val defs = (fields + missingFields).map {
            val field = it.first
            val name = field.name.substring(0, field.name.length - 2)
            val value = renderModelValue(it.second, field.concrType)
            "${complexTypeToString(field.concrType)} $name = $value;"
        }
        return defs
    }

    fun closeScopes(): String {
        var res = ""
        while (scopeLevel > 0) {
            scopeLevel -= 1
            res += indent("\n}")
        }
        return res
    }

    override fun visit(info: InfoClassPrecondition) = ""

    override fun visit(info: InfoMethodPrecondition) = ""

    override fun visit(info: InfoNullCheck) = ""

    override fun visit(info: InfoSkip) = ""

    override fun visit(info: InfoSkipEnd) = ""

    override fun visit(info: InfoInvariant) = ""

    override fun visit(info: NoInfo) = ""

    override fun visit(info: InfoAwaitUse): String {
        val postHeap = model.heapMap[info.heapExpr.toSMT()]
        val assignmentBlock = renderHeapAssignmentBlock(postHeap)

        // If the guard is a True constant, this was probably a suspend statement before translation
        // so we'll render it accordingly
        if (info.guard is Const && info.guard.name == "true")
            return indent("\n// suspend;\n$assignmentBlock\n")

        val isFutureGuard = info.guard.absExp!!.type.simpleName == "Fut"
        val maybeQuestionmark = if (isFutureGuard) "?" else ""

        val renderedGuard = "${renderExp(info.guard)}$maybeQuestionmark"

        return indent("\n// await $renderedGuard;\n$assignmentBlock\n")
    }

    override fun visit(info: InfoIfElse): String {
        val res =  indent("if(${renderExp(info.guard)}){}\nelse{")
        scopeLevel += 1

        return res
    }

    override fun visit(info: InfoIfThen): String {
        val res = indent("if(${renderExp(info.guard)}){")
        scopeLevel += 1
        return res
    }

    override fun visit(info: InfoBranch): String {
        var res = indent("case ${renderExp(info.matchExpr)} {") + "\n"
        scopeLevel += 1
        res = res + indent("${renderExp(info.pattern)} => {") + "\n"
        scopeLevel += 1
        res += indent("// Known from previous negated patterns:\n" +
                    "// ${renderFormula(info.previousConditions)}")

        return res
    }

    override fun visit(info: InfoLocAssign): String {
        val location = renderDeclLocation(info.lhs, type2str = true)

        return indent("$location = ${renderExp(info.expression)};")
    }

    override fun visit(info: InfoGetAssign): String {
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val origGet = "// $location = ${renderExp(info.expression)};"

        var futureValue = model.smtExprs[info.futureExpr.toSMT()]
        var getReplacement = ""
        if (futureValue == null) {
            getReplacement = "// Future value irrelevant or unavailable, using default:\n"
            futureValue = getDefaultValueForLocation(info.lhs)
        }

        getReplacement += renderModelAssignment(info.lhs, futureValue)

        return indent("$origGet\n$getReplacement")
    }

    override fun visit(info: InfoCallAssign): String {
        // Get location with possible type declaration both in original form and executable form
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val strLocation = renderDeclLocation(info.lhs, type2str = true)

        val origCall = "// $location = ${renderExp(info.callee)}!${renderExp(info.call)};"
        val callReplacement = "$strLocation = \"${info.futureName}\";"

        return indent("$origCall\n$callReplacement")
    }

    override fun visit(info: InfoSyncCallAssign): String {
        // Detect a stand-alone method call with no lhs
        val unitCall = if (info.lhs is ProgVar)
                info.lhs.concrType.qualifiedName == "ABS.StdLib.Unit"
            else
                (info.lhs as Field).concrType.qualifiedName == "ABS.StdLib.Unit"

        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val origCallExp = "${renderExp(info.callee)}.${renderExp(info.call)}"

        // Get heap anonymization assignments
        val postHeap = model.heapMap[info.heapExpr.toSMT()]
        val assignmentBlock = renderHeapAssignmentBlock(postHeap)

        var methodReturnVal = model.smtExprs[info.returnValExpr.toSMT()]
        var callReplacement = ""
        if (methodReturnVal == null) {
            callReplacement = "// Return value irrelevant or unavailable, using default:\n"
            methodReturnVal = getDefaultValueForLocation(info.lhs)
        }
        callReplacement += renderModelAssignment(info.lhs, methodReturnVal)

        return if (unitCall)
                indent("// $origCallExp;\n$assignmentBlock")
            else
                indent("// $location = $origCallExp;\n$assignmentBlock\n$callReplacement")
    }

    override fun visit(info: InfoLoopInitial) = indent("while(${renderExp(info.guard)}) { }")

    override fun visit(info: InfoLoopPreserves): String {
        val text = "// Known true:\n" +
            "// Loop guard: ${renderExp(info.guard)}\n" +
            "// Loop invariant: ${renderFormula(info.loopInv)}\n" +
            "// while(${renderExp(info.guard)}) {\n" +
            "{"
        val res = indent(text)

        scopeLevel += 1

        return res
    }

    override fun visit(info: InfoLoopUse): String {
        val text = "// while(${renderExp(info.guard)}){} \n" +
            "// Known true:\n" +
            "// Negated loop guard: !(${renderExp(info.guard)})\n" +
            "// Loop invariant: ${renderFormula(info.invariant)}\n"

        return indent(text)
    }

    override fun visit(info: InfoObjAlloc): String {
        // Get location with possible type declaration both in original form and executable form
        val location = renderDeclLocation(info.lhs, type2str = false, declare = false)
        val strLocation = renderDeclLocation(info.lhs, type2str = true)

        val original = "// $location = ${renderExp(info.classInit)};"
        val replacement = "$strLocation = \"${getObjectBySMT(info.newSMTExpr)}\";"
        return indent("$original\n$replacement")
    }

    override fun visit(info: InfoReturn): String {

        // Desugaring apparently inserts literal "return Unit" statements, we won't render those
        if (info.expression is SExpr && info.expression.op == "Unit")
            return indent("// return unit")

        val replacement = "println(toString(${renderExp(info.expression)})); // return statement"

        // Get the evaluation of the whole expression
        val evalValue = model.smtExprs[info.retExpr.toSMT()]
        val eval = if (evalValue == null) "Irrelevant or unavailable value" else renderModelValue(evalValue, info.expression.absExp!!.type)

        // Get evaluations of all used definitions (progVars and fields)
        val componentValues = info.retExprComponentMap.mapValues {
            model.smtExprs[it.value.toSMT()]
        }.filterValues { it != null } // There shouldn't be any null values here, but we'll discard them just in case

        // Render value and location for each component
        val renderedComponents = componentValues.map {
            val loc = if (it.key is Location) renderLocation(it.key as Location) else it.key.prettyPrint()
            val value = renderModelValue(it.value!!, it.key.absExp!!.type)
            "// $loc: $value"
        }

        var evalMsg = "// Evaluates to: $eval"
        if (renderedComponents.size > 1)
            evalMsg += "\n// Detailed evaluation breakdown:\n" + renderedComponents.joinToString("\n")

        return indent("$replacement\n$evalMsg")
    }

    override fun visit(info: InfoScopeClose): String {
        // Invalidate declarations made in the current scope
        val validDefs = varDefs.filter { it.second < scopeLevel }
        varDefs.clear()
        varDefs.addAll(validDefs)

        if (scopeLevel > 0)
            scopeLevel -= 1
        return indent("}")
    }

    private fun renderDeclLocation(loc: Location, type2str: Boolean, declare: Boolean = true): String {
        var location = renderLocation(loc)

        // Fields do not need to be declared
        if (loc !is ProgVar)
            return location

        // Futures and object types are replaced by placeholder strings
        // in executable code but kept in comments for context
        val tpe = if (type2str) complexTypeToString(loc.concrType) else renderType(loc.concrType)

        // Variables have to be declared on first use
        if (varDefs.none { it.first == location }) {
            // Remember that we declared this variable and type
            if (declare) {
                varDefs.add(Pair(location, scopeLevel))
                varTypes[location] = tpe
            }
            location = "$tpe $location"
        }
        // Edge case: Because we lose block information during translation, a variable from a closed scope
        // may be redeclared with a different type. In this case, we'll declare a renamed variable to avoid compiler issues
        else if (tpe != varTypes[location] && declare) {
            val disambName = loc.name + "_redec" + tpe

            // Remap all future occurences of the original name to the new name
            varRemaps[loc.name] = disambName
            location = disambName

            if (varDefs.none { it.first == disambName }) {
                // Remember declaration of the renamed variable
                varDefs.add(Pair(disambName, scopeLevel))
                varTypes[disambName] = tpe

                val warning = "// Warning: Due to lost scoping, variable ${loc.name} is redeclared with new type $tpe. Renaming all future occurences to $disambName"
                location = "$warning\n$tpe $disambName"
            }
        }

        return location
    }

    private fun renderLocation(loc: Location): String {
        return when (loc) {
            is ProgVar -> if (varRemaps.containsKey(loc.name)) varRemaps[loc.name]!! else loc.name
            is Field -> {
                val name = loc.name.substring(0, loc.name.length - 2) // Remove _f suffix
                usedFields.add(loc) // Remember this field so we include it in field definitions later
                "this.$name"
            }
            else -> throw Exception("Cannot render unknown location type: ${loc.prettyPrint()}")
        }
    }

    private fun renderHeapAssignmentBlock(postHeap: List<Pair<Field, ModelValue>>?): String {
        return when {
            postHeap == null -> "// No heap modification info available at this point"
            postHeap.isEmpty() -> "// Heap remains unchanged here"
            else -> {
                val assignments = postHeap.map { renderModelAssignment(it.first, it.second) }.joinToString("\n")
                "// Assume the following assignments while blocked:\n$assignments\n// End assignments"
            }
        }
    }

    private fun renderModelAssignment(loc: Location, value: ModelValue): String {
        val location = renderDeclLocation(loc, type2str = true)

        val type = when (loc) {
            is Field -> loc.concrType
            is ProgVar -> loc.concrType
            else -> throw Exception("Cannot render unknown location: ${loc.prettyPrint()}")
        }

        return "$location = ${renderModelValue(value, type)};"
    }

    private fun renderModelValue(value: ModelValue, ctype: Type): String {
        val dType = ctype.qualifiedName
        return when {
            dType == "ABS.StdLib.Int" -> (value as MvInteger).value.toString()
            dType == "ABS.StdLib.Fut" -> "\"${model.futNameById((value as MvInteger).value)}\""
            dType == "ABS.StdLib.Bool" -> if ((value as MvBoolean).value) "True" else "False"
            dType == "<UNKNOWN>" -> "\"unknownType($value)\""
            isDataType(dType) -> (value as MvDataType).toString()
            value is MvInteger -> if (value.value == 0) "null" else "\"${getObjectById(value.value)}\""
            else -> throw Exception("Cannot render model value of unknown type $dType")
        }
    }

    private fun getDefaultValueForType(ctype: Type): ModelValue {
        val dType = ctype.qualifiedName
        return when {
            isDataType(dType) -> {
                // Data types are tricky
                // We'll try to generate a short-as-possible default value by choosing the type constructor with the fewest parameters
                // If we can't find one with no parameters, we recursively generate default values for the required parameters
                val typeDecl = ADTRepos.getDeclForType(dType)
                val preferredConstructor = typeDecl.dataConstructorList.minBy { it.constructorArgList.toList().size }!!
                if (preferredConstructor.constructorArgList.toList().isEmpty())
                    MvDataType(preferredConstructor.qualifiedName)
                else {
                    val params = preferredConstructor.constructorArgList.map { getDefaultValueForType(it.type) }
                    MvDataType(preferredConstructor.qualifiedName, params)
                }
            }
            dType == "ABS.StdLib.Bool" -> MvBoolean(false)
            else -> MvInteger(0)
        }
    }

    private fun getDefaultValueForLocation(loc: Location): ModelValue {
        val type = when (loc) {
            is Field -> loc.concrType
            is ProgVar -> loc.concrType
            else -> throw Exception("Cannot get default value for unknown location: ${loc.prettyPrint()}")
        }
        return getDefaultValueForType(type)
    }

    private fun getObjectBySMT(smtRep: String): String {
        if (!objMap.containsKey(smtRep)) {
            objectCounter++
            objMap[smtRep] = "object_$objectCounter"
        }

        return objMap[smtRep]!!
    }

    private fun getObjectById(id: Int): String {
        if (!model.objLookup.containsKey(id))
            return "object_?($id)"

        val smtRep = model.objLookup[id]!!
        return getObjectBySMT(smtRep)
    }

    private fun renderType(type: Type) = stripModulePrefix(type.qualifiedName)

    private fun renderExp(e: Expr): String {
        // Keep track of fields referenced in expressions for field declarations
        usedFields.addAll(collectBaseExpressions(e).filterIsInstance<Field>())
        return renderExpression(e, varRemaps)
    }

    // Public to allow rendering of formulas with correct replacements from elsewhere
    fun renderFormula(formula: Formula) = renderFormula(formula, varRemaps)

    private fun indent(text: String) = indent(text, scopeLevel)
}

fun complexTypeToString(ctype: Type): String {
    val type = ctype.qualifiedName
    return if (type == "ABS.StdLib.Int" || type == "ABS.StdLib.Bool" || isDataType(type))
        stripModulePrefix(type)
    else
        "String"
}

fun stripModulePrefix(type: String): String {
    // Delete everything up to and including the last dot
    return type.replace(Regex("^.*\\."), "")
}

fun isDataType(dType: String): Boolean {
    val prefix = ADTRepos.libPrefix(dType)
    return prefix != "Int" && ADTRepos.getAllTypePrefixes().contains(prefix)
}

fun indent(text: String, level: Int, indentString: String = "\t"): String {
    val lines = text.split("\n")
    val spacer = indentString.repeat(level)

    return lines.map { "$spacer$it" }.joinToString("\n")
}
