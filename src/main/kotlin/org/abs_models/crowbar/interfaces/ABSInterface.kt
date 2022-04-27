package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.FunctionRepos
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.ast.AssertStmt
import org.abs_models.frontend.ast.AssignStmt
import org.abs_models.frontend.ast.AwaitStmt
import org.abs_models.frontend.ast.IfStmt
import org.abs_models.frontend.ast.ReturnStmt
import org.abs_models.frontend.ast.Stmt
import org.abs_models.frontend.ast.ThrowStmt
import org.abs_models.frontend.ast.WhileStmt
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType

/**
 *   Translates the ABS AST into our IR
 */

fun translateStatement(input: Stmt?, subst: Map<String, Expr>, AEsubst : MutableMap<ProgVar, AEExpr> = mutableMapOf() ) : org.abs_models.crowbar.data.Stmt {
    if(input == null) return SkipStmt
    val returnType =
        if(input.contextMethod != null) input.contextMethod.type
        else UnknownType.INSTANCE



    if(input.hasAnnotation()){
        val abstractElements = translateAnnotation(input, subst, AEsubst)

        //This deals with the case of a last abstract expression (not good by the way) it will be changed and generalised or not...

        //output("\n$abstractElements")

        var next = input

        if (abstractElements.lastOrNull() is AEExpr && input is VarDeclStmt){
            var abstractExp = abstractElements.removeLast() as AEExpr
            abstractExp.concrType = input.varDecl.type
            AEsubst[ProgVar(input.varDecl.name, input.varDecl.type)] = abstractExp
            next = org.abs_models.frontend.ast.SkipStmt()
        }

        //output("$abstractElements\n")

        return abstractElements.foldRight(translateStatement(next, subst, AEsubst)) { nx, acc ->
            appendStmt(
                nx as AEStmt,
                acc
            )
        }
    }

    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return SkipStmt
        is ExpressionStmt ->{
            val loc = FreshGenerator.getFreshProgVar(input.type)
            val exp = input.exp
            val type = input.type
            return when(exp) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst, AEsubst), extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst, AEsubst))
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst, AEsubst), translateExpression(exp, returnType, subst, AEsubst) as CallExpr)
                is SyncCall     -> desugar(loc, type, exp, returnType, subst, AEsubst)
                else            -> ExprStmt(translateExpression(exp, returnType, subst, AEsubst)) // Cannot be SkipStmt, as an expression can throw an exception
            }
        }
        is VarDeclStmt -> {
            val loc = ProgVar(input.varDecl.name, input.varDecl.type)
            return when(val exp = input.varDecl.initExp ?: NullExp()) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst, AEsubst), extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst, AEsubst))
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst, AEsubst), translateExpression(exp, returnType, subst, AEsubst) as CallExpr)
                is SyncCall     -> desugar(loc, input.type, exp, returnType, subst, AEsubst)
                else -> org.abs_models.crowbar.data.AssignStmt(loc, translateExpression(exp, returnType, subst, AEsubst))
            }
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name+"_f",input.varNoTransform.type)
            else ProgVar(
                input.varNoTransform.name,
                input.varNoTransform.type
            )
            return when(val exp = input.valueNoTransform) {
                is GetExp       -> SyncStmt(loc, translateExpression(exp, returnType, subst, AEsubst), extractResolves(input), FreshGenerator.getFreshPP())
                is NewExp       -> AllocateStmt(loc, translateExpression(exp, returnType, subst, AEsubst))
                is AsyncCall    -> CallStmt(loc, translateExpression(exp.callee, returnType, subst, AEsubst), translateExpression(exp, returnType, subst, AEsubst) as CallExpr)
                is SyncCall     -> desugar(loc, input.type, exp, returnType, subst, AEsubst)
                else -> org.abs_models.crowbar.data.AssignStmt(loc, translateExpression(exp, returnType, subst, AEsubst))
            }
        }
        is Block -> {
            val subs = input.stmts.map {translateStatement(it, subst, AEsubst)  }
            if(subs.isEmpty())  return SkipStmt
            val last = subs.last()
            val tail = subs.dropLast(1)
            return tail.foldRight( last) { nx, acc -> appendStmt(nx, acc) }
        }
        is WhileStmt -> {
            return org.abs_models.crowbar.data.WhileStmt(translateExpression(input.conditionNoTransform, returnType, subst, AEsubst),
                translateStatement(input.bodyNoTransform, subst, AEsubst),
                FreshGenerator.getFreshPP(),
                extractSpec(input,"WhileInv", returnType))
        }
        is AwaitStmt -> return org.abs_models.crowbar.data.AwaitStmt(translateGuard(input.guard, returnType, subst, AEsubst),FreshGenerator.getFreshPP())
        is SuspendStmt -> return org.abs_models.crowbar.data.AwaitStmt(Const("true", input.model.boolType),FreshGenerator.getFreshPP()) // We should be able to model a suspend; as an await True;
        is ReturnStmt -> return org.abs_models.crowbar.data.ReturnStmt(translateExpression(input.retExp, returnType, subst, AEsubst))
        is IfStmt -> return org.abs_models.crowbar.data.IfStmt(translateExpression(input.conditionNoTransform, returnType, subst, AEsubst), translateStatement(input.then, subst, AEsubst), translateStatement(input.`else`, subst, AEsubst))
        is AssertStmt -> return org.abs_models.crowbar.data.AssertStmt(translateExpression(input.condition, returnType, subst, AEsubst))
        is CaseStmt -> {
            var list : List<Branch> = emptyList()
            for (br in input.branchList) {
                val patt = translatePattern(br.left, input.expr.type, returnType, subst)
                val next = translateStatement(br.right, subst, AEsubst)
                list = list + Branch(patt, next)
            }
            return BranchStmt(translateExpression(input.expr, returnType, subst, AEsubst), BranchList(list))
        }
        is DieStmt -> return org.abs_models.crowbar.data.AssertStmt(Const("False", input.model.boolType))
        is MoveCogToStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is DurationStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is ThrowStmt -> return org.abs_models.crowbar.data.ThrowStmt(translateExpression(input.reason, returnType, subst, AEsubst))
        is TryCatchFinallyStmt -> {
            val inner = translateStatement(input.body, subst, AEsubst)
            var list : List<Branch> = emptyList()
            for (br in input.catchList) {
                val patt = translatePattern(br.left, returnType, input.model.exceptionType, subst)
                val next = translateStatement(br.right, subst, AEsubst)
                list = list + Branch(patt, next)
            }
            val pp = FreshGenerator.getFreshPP()
            val finally = translateStatement(input.finally, subst, AEsubst)
            val sFirst = TryPushStmt(ConcreteExceptionScope(BranchList(list), finally, pp))
            return appendStmt(appendStmt(sFirst, inner), TryPopStmt(pp))
        }
        //this is the foreach statement only and should not occur
        else -> throw Exception("Translation of ${input::class} not supported, please flatten the model before passing it to Crowbar" )
    }
}

/**
 *  Function to extract abstract program elements from a statement ,it returns a list of abstract program elements while cleaning the input of its annotations
 */

fun translateAnnotation(input : Stmt, subst: Map<String, Expr>, AEsubst: MutableMap<ProgVar, AEExpr>) : MutableList<AEProgramElement>{
    val abstractProg : MutableList<AEProgramElement> = emptyList<AEProgramElement>().toMutableList()

    var spec : AESpec

    var accessible : MutableSet<Pair<Boolean, String>> = mutableSetOf()
    var assignable : MutableSet<Pair<Boolean, String>> = mutableSetOf()
    var retBehavior : Expr = Const("false")
    var excBehavior : Expr = Const("false")
    var normBehavior : Expr = Const("true")

    loop@ for(annotation in input.annotations){
        if(annotation.value is StringLiteral){
            try {
                spec = AbstractParser.parse((annotation.value as StringLiteral).content)
            }
            catch (e : Exception) {
                output("Exception in string annotation parsing, continuing: ${e.message}")
                continue
            }

            when(spec){
                is AEStatement      -> {
                    abstractProg.add(
                        AEStmt(
                            ConcreteName(spec.name),
                            AELocSet(accessible.map{pair -> Pair(pair.first, AELocation(pair.second))}),
                            AELocSet(assignable.map{pair -> Pair(pair.first, AELocation(pair.second))}),
                            normBehavior,
                            retBehavior
                        )
                    )
                    accessible = mutableSetOf()
                    assignable = mutableSetOf()
                    retBehavior = Const("false")
                    normBehavior = Const("true")
                    excBehavior = Const("false")
                }
                is AEExpression     -> {
                    abstractProg.add(
                        AEExpr(
                            ConcreteName(spec.name),
                            AELocSet(accessible.map{pair -> Pair(pair.first, AELocation(pair.second))}),
                            AELocSet(assignable.map{pair -> Pair(pair.first, AELocation(pair.second))}),
                            excBehavior
                        )
                    )
                    accessible = mutableSetOf()
                    assignable = mutableSetOf()
                    retBehavior = Const("false")
                    excBehavior = Const("false")
                }
                is AEAccessible     -> accessible.addAll(spec.id_locs.map { Pair(false,it.getName()) })
                is AEAssignable     -> assignable.addAll(spec.id_locs.map { if(it is AEHasToLoc)Pair(true, it.getName()) else Pair(false, it.getName()) })
                is AERetBehavior    -> output("Return Behavior not yet supported, ignored for now.")
                is AENormBehavior   -> normBehavior = translatePhi(spec.phi, subst, AEsubst)
                else                -> output("Unusual annotation, ignored ${spec.prettyPrint()}")
            }
        }
    }

    input.annotationList = List()

    return abstractProg
}

fun translatePhi(input: AEPhi, subst: Map<String, Expr>, aeSubst: MutableMap<ProgVar, AEExpr> = mutableMapOf()) : Expr {
    return when(input) {
        is AEInstantiatedPhi    -> PhiExpr(input.id_formula, AELocation(input.id_formula))
        is AENot                -> SExpr("!", listOf(translatePhi(input.phi, subst, aeSubst)))
        is AEImpl               -> SExpr("->", listOf(translatePhi(input.ante, subst, aeSubst), translatePhi(input.succ, subst, aeSubst)))
        is AEAnd                -> SExpr("&&", listOf(translatePhi(input.left, subst, aeSubst), translatePhi(input.right, subst, aeSubst)))
        is AEOr                 -> SExpr("||", listOf(translatePhi(input.left, subst, aeSubst), translatePhi(input.right, subst, aeSubst)))
        is AETrue               -> Const("true")
        is AEFalse              -> Const("false")
        is AEPred               -> SExpr(input.op, listOf(translatePhi(input.left, subst, aeSubst), translatePhi(input.right, subst, aeSubst)))
        is AEVar                -> ProgVar(input.id)
        is AEInt                -> Const("${input.value}")
        else                    -> throw Exception("Unforeseen AEPhi in translatePhi : $input")
    }
}

fun translateExpression(input: Exp, returnType: Type, subst : Map<String, Expr>, AEsubst : MutableMap<ProgVar, AEExpr> = mutableMapOf()) : Expr {

    val converted = when(input){
        is FieldUse -> {
            if(input.contextDecl is InterfaceDecl)
                throw Exception("fields cannot be referred to in the declaration of interfaces: " +
                        "field $input is referred to in the declaration of ${input.contextDecl.name}")
            val type = if (input.type.isUnknownType) {
                            if(input.contextDecl.locallookupVarOrFieldName(input.name, true) == null)
                                throw Exception("Field ${input.name} not defined")
                            input.contextDecl.locallookupVarOrFieldName(input.name, true).type
                        } else input.type
            Field(input.name + "_f",type)
        }
        is LetExp          ->
            translateExpression(input.exp, returnType, subst + Pair(input.`var`.name, translateExpression(input.`val`, returnType, subst, AEsubst)), AEsubst) //this handles overwrite correctly
        is IntLiteral      -> Const(input.content, input.model.intType)
        is GetExp          -> readFut(translateExpression(input.pureExp, returnType, subst, AEsubst))
        is NewExp          -> FreshGenerator.getFreshObjectId(input.type.qualifiedName, input.paramList.map { translateExpression(it, returnType, subst, AEsubst) },input.type) //todo:add "implements" information to Repos
        is NullExp         -> Const("0", input.model.intType)
        is ThisExp         -> Const("1", input.model.intType)
        is VarUse -> {
            if (input.name == "result") {
                if (returnType.isUnknownType)
                    throw Exception("result type cannot be <UNKNOWN>")
                ReturnVar(returnType.qualifiedName,returnType)
            } else {
                if (input.type.isFutureType) {
                    ProgVar(input.name, input.type)
                }
                else if(subst.keys.contains(input.name)){
                    subst[input.name]
                } else {
                    val aux = ProgVar(input.name, input.type)
                    if (AEsubst.containsKey(aux)){
                        AEsubst.remove(aux)
                    }
                    else
                        aux
                }
            }
        }
        is Binary -> {
            val op = when (input) {
                is GTEQExp -> ">="
                is LTEQExp -> "<="
                is GTExp -> ">"
                is LTExp -> "<"
                is EqExp -> "="
                is NotEqExp -> "!="
                is AddAddExp -> "+"
                is SubAddExp -> "-"
                is MultMultExp -> "*"
                is DivMultExp -> "/"
                is AndBoolExp -> "&&"
                is OrBoolExp -> "||"
                else -> throw Exception("Translation of data ${input::class} not supported, term is $input")
            }
            SExpr(op, listOf(translateExpression(input.left, returnType, subst, AEsubst), translateExpression(input.right, returnType, subst, AEsubst)))
        }
        is Unary -> {
            val op = when(input){
                is MinusExp     -> "-"
                is NegExp       -> "!"
                else            -> throw Exception("Translation of data ${input::class} not supported, term is $input" )
            }
            SExpr(op, listOf(translateExpression(input.operand, returnType, subst, AEsubst)))
        }
        is DataConstructorExp -> {
            if(input.dataConstructor == null){
                throw Exception("Data constructor ${input.constructor} not defined")
            }
            if(input.type.isUnknownType)
                throw Exception("Wrong use of data constructor ${input.constructor} with parameters ${input.paramList} ")
            when (input.dataConstructor!!.name) {
                "Unit" -> unitExpr()
                "True" -> Const("true", input.model.boolType)
                "False" -> Const("false", input.model.boolType)
                else -> DataTypeExpr(input.dataConstructor!!.qualifiedName, input.type.qualifiedName, input.type, input.params.map { translateExpression(it, returnType, subst, AEsubst) })
            }
        }
        is FnApp ->
            if (input.name == "valueOf")
                readFut(translateExpression(input.params.getChild(0), returnType, subst, AEsubst))
            else if (input.name == "hasRole") {
                val roleConst = Const("\"${(input.params.getChild(1) as StringLiteral).content}\"", input.model.stringType)
                val field = translateExpression(input.params.getChild(0), returnType, subst, AEsubst)
                SExpr("hasRole", listOf(field, roleConst))
            }
            else if (input.decl is UnknownDecl) {
                if (specialHeapKeywords.containsKey(input.name))
                    SExpr(input.name, input.params.map { translateExpression(it, returnType, subst, AEsubst) })
                else
                    throw Exception("Unknown declaration of function ${input.name}")
            } else if (FunctionRepos.isKnown(input.decl.qualifiedName)) {
                SExpr(input.decl.qualifiedName.replace(".", "-"), input.params.map { translateExpression(it, returnType, subst, AEsubst) })
            } else if(input.decl.qualifiedName == "ABS.StdLib.random"){
                FreshGenerator.getFreshProgVar(input.model.intType)
            } else throw Exception("Translation of FnApp is not fully supported, term is $input with function ${input.decl.qualifiedName}")
        is IfExp -> SExpr("ite", listOf(translateExpression(input.condExp, returnType, subst, AEsubst),translateExpression(input.thenExp, returnType, subst, AEsubst),translateExpression(input.elseExp, returnType, subst, AEsubst)))
        is Call -> {
            val met = input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name
            val params = input.params.map {  translateExpression(it, returnType, subst, AEsubst) }

            if(input is AsyncCall || input.callee  !is ThisExp)
                CallExpr(met, params)
            else
                SyncCallExpr(met, params)
        }
        is CaseExp ->{
            CaseExpr(translateExpression(input.expr, returnType, subst, AEsubst),
                ADTRepos.libPrefix(input.type.qualifiedName),
                input.branchList.map {
                BranchExpr(
                    translatePattern(it.left, it.patternExpType, returnType, subst),
                    translateExpression(it.right, returnType, subst, AEsubst))}, input.freeVars)
        }
        is StringLiteral -> {
            Const("\"" + input.content +"\"", input.model.stringType)
        }
        is FloatLiteral -> {
            Const(input.content, input.model.floatType)
        }
        is AsExp -> {
            val inputExpr = translateExpression(input.exp,returnType, subst, AEsubst)
            val implements = ImplementsExpr(inputExpr,input.type)
            val res = SExpr("ite",
                listOf(
                    SExpr("and", listOf(SExpr("not", listOf(SExpr("=", listOf(inputExpr, Const("0", input.model.intType))))),
                    implements)),
                    inputExpr,
                    Const("0", input.model.intType)))
            res
        }
        is ImplementsExp -> {
            ImplementsExpr(translateExpression(input.exp, returnType, subst, AEsubst), input.interfaceTypeUse.type)
        }
        else -> throw Exception("Translation of ${input::class} not supported, term is $input" )
    }

    // Save reference to original expression
    converted!!.absExp = input
    return converted
}

fun translateGuard(input: Guard, returnType: Type, subst: Map<String, Expr>, AEsubst: MutableMap<ProgVar, AEExpr> = mutableMapOf()) : Expr =
    when(input){
        is ExpGuard -> translateExpression(input.pureExp, returnType, subst, AEsubst)
        is AndGuard -> SExpr("&&",listOf(translateGuard(input.left, returnType, subst, AEsubst), translateGuard(input.right, returnType, subst, AEsubst)))
        is ClaimGuard -> {
            val placeholder = Const("true")
            placeholder.absExp = input.`var` // Save reference to original guard expression
            placeholder
        }
        else -> throw Exception("Guards ${input::class} are not coreABS" )
    }

fun translatePattern(pattern : Pattern, overrideType : Type, returnType:Type, subst: Map<String, Expr>, AEsubst: MutableMap<ProgVar, AEExpr> = mutableMapOf()) : Expr =
    when (pattern) {
        is PatternVarUse -> ProgVar(pattern.name, pattern.type)
        is PatternVar -> ProgVar(pattern.`var`.name, pattern.type)
        is LiteralPattern -> translateExpression(pattern.literal, returnType, subst, AEsubst)
        is UnderscorePattern ->  FreshGenerator.getFreshProgVar(overrideType)
        is ConstructorPattern -> {
            val qualName = if(returnType == pattern.moduleDecl.model.exceptionType) "ABS.StdLib.Exceptions.${pattern.constructor}" else typeWithModule(pattern.constructor, pattern.moduleDecl.name)
            DataTypeExpr(qualName,pattern.type.qualifiedName,pattern.type,pattern.params.map { translatePattern(it,it.inhType, returnType, subst) })
        }
        else -> throw Exception("Translation of complex constructors is not supported")
        }

fun typeWithModule(type : String, moduleName : String) :String {
    var constructor = type
    if(!constructor.startsWith("$moduleName."))
        constructor =  "$moduleName.$type"
    return constructor
}

fun filterAtomic(input: Stmt?, app : (Stmt) -> Boolean) : Set<Stmt> {
    if (input == null) return emptySet()
    return when (input) {
        is Block -> input.stmts.fold(emptySet()) { acc, nx -> acc + filterAtomic(nx, app) }
        is WhileStmt -> filterAtomic(input.body, app)
        is IfStmt -> filterAtomic(input.then, app) + filterAtomic(input.`else`, app)
        else -> if (app(input)) setOf(input) else emptySet()
    }
}

/* Extracts the resolves set for get statements */
fun extractResolves(stmt: Stmt): ConcreteStringSet{
    val spec = stmt.annotations.firstOrNull { it.type.toString()
        .endsWith(".Spec") && it.value is DataConstructorExp && (it.value as DataConstructorExp).constructor == "Resolves" }
        ?: return ConcreteStringSet()
    val inner = ((spec.value as DataConstructorExp).params.getChild(0) as StringLiteral).content.split(",").map { it.trim() }
    return ConcreteStringSet(inner.toSet())
}

/* We need to perform the rewriting on sync call ourselves as the version of the compiler we use still uses the old broken location types */
fun desugar(loc: Location, type: Type, syncCall: SyncCall, returnType :Type, subst: Map<String, Expr>, AEsubst: MutableMap<ProgVar, AEExpr> = mutableMapOf()) : org.abs_models.crowbar.data.Stmt{
    val calleeExpr = translateExpression(syncCall.callee, returnType, subst, AEsubst)
    val callExpr = translateExpression(syncCall, returnType, subst, AEsubst)

    if(syncCall.callee is ThisExp)
        return SyncCallStmt(loc, calleeExpr, callExpr as SyncCallExpr)

    val fut = FreshGenerator.getFreshProgVar(type)
    val callStmt = CallStmt(fut, calleeExpr, callExpr as CallExpr)
    val syncStmt = SyncStmt(loc, readFut(fut), ConcreteStringSet(setOf(syncCall.methodSig.name)), FreshGenerator.getFreshPP())
    return SeqStmt(callStmt, syncStmt)
}


// Extract implicit disjoints relations

fun extractDisjoint(input : Stmt?, locations : Set<Location>, scope : List<Set<Location>>) : Set<Set<Location>> {
    if(input == null){
        return emptySet()
    }

    val disjoint : MutableSet<Set<Location>> = mutableSetOf()

    var spec:AESpec
    for(annotation in input.annotationList){
        if(annotation.value is StringLiteral) {
            try {
                spec = AbstractParser.parse((annotation.value as StringLiteral).content)
            } catch (e: Exception) {
                output("Exception in string annotation parsing, continuing: ${e.message}")
                continue
            }

            val usedLocation : MutableList<Location> = mutableListOf()

            when(spec){
                is AEAccessible -> {
                    usedLocation += spec.id_locs.map { loc ->
                        loc.getName()
                    }.map { name ->
                        locFromName(name, locations)
                    }
                }
                is AEAssignable -> {
                    usedLocation += spec.id_locs.map { loc ->
                        loc.getName()
                    }.map { name ->
                        locFromName(name, locations)
                    }
                }
                else -> continue
            }

            val absentLoc = locations.minus(scope.fold(emptySet(), Set<Location>::plus))
            for(aloc in absentLoc){
                for(uloc in usedLocation){
                    disjoint += setOf(aloc, uloc)
                }
            }
        }
    }

    when(input){
        is VarDeclStmt -> return disjoint
        is Block -> {
            val localScope = mutableSetOf<Location>()
            for (stmt in input.stmts) {
                val testscope = scope.toMutableList()
                testscope.add(localScope.toSet())
                disjoint += extractDisjoint(stmt, locations, testscope)
                if (stmt is VarDeclStmt)
                    localScope += extractLocation(stmt)
            }
            return disjoint
        }
        is IfStmt -> return disjoint + extractDisjoint(input.then, locations, scope) + extractDisjoint(input.`else`,locations, scope)
        is WhileStmt -> throw Exception("While scope computation not yet supported.")
        else -> return disjoint
    }
}

fun locFromName(name: String, locations : Set<Location>): Location {
    return if (locations.contains(Field(name))) {
        Field(name)
    } else if (locations.contains(ProgVar(name))) {
        ProgVar(name)
    } else {
        AELocation(name)
    }
}

// Extract the locations

fun extractLocation(input: Stmt?): Set<Location>{
    return when(input){
        is org.abs_models.frontend.ast.SkipStmt -> emptySet()
        is ExpressionStmt -> emptySet()
        is VarDeclStmt -> setOf(ProgVar(input.varDecl.name, input.varDecl.type))
        is AssignStmt -> emptySet()
        is Block -> input.stmts.map { extractLocation(it) }.flatten().toSet()
        is WhileStmt -> extractLocation(input.bodyNoTransform)
        is AwaitStmt -> emptySet()
        is SuspendStmt -> emptySet()
        is ReturnStmt -> emptySet()
        is IfStmt -> extractLocation(input.then) + extractLocation(input.`else`)
        is AssertStmt -> emptySet()
        is CaseStmt -> {
            var res : Set<Location> = emptySet()
            for (br in input.branchList) {
                res += extractLocation(br.right)
            }
            res
        }
        is DieStmt -> emptySet()
        is MoveCogToStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is DurationStmt -> throw Exception("Statements ${input::class} are not coreABS" )
        is ThrowStmt -> emptySet()
        is TryCatchFinallyStmt -> {
            var res = extractLocation(input.body)
            for (br in input.catchList) {
                res += extractLocation(br.right)
            }
            res += extractLocation(input.finally)
            res
        }
        else        -> emptySet()
    }
}