package org.abs_models.crowbar.interfaces

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Const
import org.abs_models.crowbar.data.SkipStmt
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.main.FunctionRepos
import org.abs_models.crowbar.main.extractSpec
import org.abs_models.crowbar.rule.FreshGenerator
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.ast.AssignStmt
import org.abs_models.frontend.ast.AwaitStmt
import org.abs_models.frontend.ast.IfStmt
import org.abs_models.frontend.ast.ReturnStmt
import org.abs_models.frontend.ast.Stmt
import org.abs_models.frontend.ast.WhileStmt
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType

fun translateABSExpToSymExpr(input: Exp, returnType: Type) : Expr {

    val converted = when(input){
        is FieldUse -> {
            if(input.contextDecl is InterfaceDecl)
                throw Exception("fields cannot be referred to in the declaration of interfaces: " +
                        "field $input is referred to in the declaration of ${input.contextDecl.name}")
            val type = if (input.type.isUnknownType) {
                if(input.contextDecl.locallookupVarOrFieldName(input.name, true) == null)
                    throw Exception("Field ${input.name} not defined")
                input.contextDecl.locallookupVarOrFieldName(input.name, true).type
            } else
                input.type
            Field(input.name + "_f", type.qualifiedName,type)
        }
        is IntLiteral -> Const(input.content)
        is GetExp          -> readFut(translateABSExpToSymExpr(input.pureExp, returnType))
        is NewExp          -> FreshGenerator.getFreshObjectId(input.className, input.paramList.map { translateABSExpToSymExpr(it, returnType) })
        is NullExp         -> Const("0")
        is ThisExp         -> Const("1")
        is VarUse -> {
            if (input.name == "result") {
                if (returnType.isUnknownType)
                    throw Exception("result type cannot be <UNKNOWN>")
                ReturnVar(returnType.qualifiedName,returnType)
            } else {
                if (input.type.isFutureType) {
                    ProgVar(input.name, (input.type as DataTypeType).getTypeArg(0).qualifiedName, input.type)
                }
                else
                    ProgVar(input.name, input.type.qualifiedName, input.type)
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
            SExpr(op, listOf(translateABSExpToSymExpr(input.left, returnType), translateABSExpToSymExpr(input.right, returnType)))
        }
        is Unary -> {
            val op = when(input){
                is MinusExp     -> "-"
                is NegExp       -> "!"
                else            -> throw Exception("Translation of data ${input::class} not supported, term is $input" )
            }
            SExpr(op, listOf(translateABSExpToSymExpr(input.operand, returnType)))
        }
        is DataConstructorExp -> {
            if(input.dataConstructor == null){
                throw Exception("Data constructor ${input.constructor} not defined")
            }
            if(input.type.isUnknownType)
                throw Exception("Wrong use of data constructor ${input.constructor} with parameters ${input.paramList} ")
            when (input.dataConstructor!!.name) {
                "Unit" -> unitExpr()
                "True" -> Const("true")
                "False" -> Const("false")
                else -> DataTypeExpr(input.dataConstructor!!.qualifiedName, input.type.qualifiedName, input.type, input.params.map { translateABSExpToSymExpr(it, returnType) })
            }
        }
        is FnApp ->
            if (input.name == "valueOf")
                readFut(translateABSExpToSymExpr(input.params.getChild(0), returnType))
            else if (input.name == "hasRole") {
                val roleConst = Const("\"${(input.params.getChild(1) as StringLiteral).content}\"")
                val field = translateABSExpToSymExpr(input.params.getChild(0), returnType)
                SExpr("hasRole", listOf(field, roleConst))
            }
            else if (input.decl is UnknownDecl) {
                if (specialHeapKeywords.containsKey(input.name))
                    SExpr(input.name, input.params.map { translateABSExpToSymExpr(it, returnType) })
                else
                    throw Exception("Unknown declaration of function ${input.name}")
            } else if (FunctionRepos.isKnown(input.decl.qualifiedName)) {
                SExpr(input.decl.qualifiedName.replace(".", "-"), input.params.map { translateABSExpToSymExpr(it, returnType) })
            } else throw Exception("Translation of FnApp is not fully supported, term is $input with function ${input.name}")
        is IfExp -> SExpr("ite", listOf(translateABSExpToSymExpr(input.condExp, returnType),translateABSExpToSymExpr(input.thenExp, returnType),translateABSExpToSymExpr(input.elseExp, returnType)))
        is Call -> {
            val met = input.methodSig.contextDecl.qualifiedName+"."+input.methodSig.name
            val params = input.params.map {  translateABSExpToSymExpr(it, returnType) }

            if(input is AsyncCall || input.callee  !is ThisExp)
                CallExpr(met, params)
            else
                SyncCallExpr(met, params)
        }
        is CaseExp ->{
            CaseExpr(translateABSExpToSymExpr(input.expr, returnType),
                ADTRepos.libPrefix(input.type.qualifiedName),
                input.branchList.map {
                BranchExpr(
                    translateABSPatternToSymExpr(it.left, it.patternExpType, returnType),
                    translateABSExpToSymExpr(it.right, returnType))}, input.freeVars)
        }
        else -> throw Exception("Translation of ${input::class} not supported, term is $input" )
    }

    // Save reference to original expression
    converted.absExp = input
    return converted
}

fun translateABSStmtToSymStmt(input: Stmt?) : org.abs_models.crowbar.data.Stmt {
    if(input == null) return SkipStmt
    val returnType =
            if(input.contextMethod != null)
                input.contextMethod.type
            else
                UnknownType.INSTANCE
    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return SkipStmt
        is ExpressionStmt ->{
            val loc = FreshGenerator.getFreshProgVar(input.type)
            val exp = input.exp
            val type = input.type
            return when(exp) {
                is GetExp       -> SyncStmt(loc, translateABSExpToSymExpr(exp, returnType))
                is NewExp       -> AllocateStmt(loc, translateABSExpToSymExpr(exp, returnType))
                is AsyncCall    -> CallStmt(loc, translateABSExpToSymExpr(exp.callee, returnType), translateABSExpToSymExpr(exp, returnType) as CallExpr)
                is SyncCall     -> desugaring(loc, type, exp, returnType)
                else -> throw Exception("Translation of ${input.exp::class} in an expression statement is not supported" )
                }
        }
        is VarDeclStmt -> {
            val loc = ProgVar(input.varDecl.name, input.varDecl.type.qualifiedName, input.varDecl.type)
            return when(val exp = input.varDecl.initExp ?: NullExp()) {
                is GetExp       -> SyncStmt(loc, translateABSExpToSymExpr(exp, returnType))
                is NewExp       -> AllocateStmt(loc, translateABSExpToSymExpr(exp, returnType))
                is AsyncCall    -> CallStmt(loc, translateABSExpToSymExpr(exp.callee, returnType), translateABSExpToSymExpr(exp, returnType) as CallExpr)
                is SyncCall     -> desugaring(loc, input.type, exp, returnType)
                else -> org.abs_models.crowbar.data.AssignStmt(loc, translateABSExpToSymExpr(exp, returnType))
            }
        }
        is AssignStmt -> {
            val loc:Location = if(input.varNoTransform is FieldUse) Field(input.varNoTransform.name+"_f", input.varNoTransform.type.qualifiedName,input.varNoTransform.type)
                               else ProgVar(
                input.varNoTransform.name,
                input.varNoTransform.type.qualifiedName,
                input.varNoTransform.type
            )
            return when(val exp = input.valueNoTransform) {
                is GetExp       -> SyncStmt(loc, translateABSExpToSymExpr(exp, returnType))
                is NewExp       -> AllocateStmt(loc, translateABSExpToSymExpr(exp, returnType))
                is AsyncCall    -> CallStmt(loc, translateABSExpToSymExpr(exp.callee, returnType), translateABSExpToSymExpr(exp, returnType) as CallExpr)
                is SyncCall     -> desugaring(loc, input.type, exp, returnType)
                else -> org.abs_models.crowbar.data.AssignStmt(loc, translateABSExpToSymExpr(exp, returnType))
            }
        }
        is Block -> {
            val subs = input.stmts.map {translateABSStmtToSymStmt(it)  }
            if(subs.isEmpty())  return SkipStmt
            val last = subs.last()
            val tail = subs.dropLast(1)
            return tail.foldRight( last , {nx, acc -> SeqStmt(nx, acc) })
        }
        is WhileStmt -> {
            return org.abs_models.crowbar.data.WhileStmt(translateABSExpToSymExpr(input.conditionNoTransform, returnType),
                                                         translateABSStmtToSymStmt(input.bodyNoTransform),
                                                         FreshGenerator.getFreshPP(),
                                                         extractSpec(input,"WhileInv", returnType))
        }
        is AwaitStmt -> return org.abs_models.crowbar.data.AwaitStmt(translateABSGuardToSymExpr(input.guard, returnType),FreshGenerator.getFreshPP())
        is SuspendStmt -> return org.abs_models.crowbar.data.AwaitStmt(Const("true"),FreshGenerator.getFreshPP()) // We should be able to model a suspend; as an await True;
        is ReturnStmt -> return org.abs_models.crowbar.data.ReturnStmt(translateABSExpToSymExpr(input.retExp, returnType))
        is IfStmt -> return org.abs_models.crowbar.data.IfStmt(translateABSExpToSymExpr(input.conditionNoTransform, returnType), translateABSStmtToSymStmt(input.then), translateABSStmtToSymStmt(input.`else`))
        is CaseStmt -> {
            var list : List<Branch> = emptyList()
            for (br in input.branchList) {
                val patt = translateABSPatternToSymExpr(br.left, input.expr.type, returnType)
                val next = translateABSStmtToSymStmt(br.right)
                list = list + Branch(patt, next)
            }
            return BranchStmt(translateABSExpToSymExpr(input.expr, returnType), BranchList(list))
        }
        else -> throw Exception("Translation of ${input::class} not supported" )
    }
}


fun desugaring(loc: Location, type: Type, syncCall: SyncCall, returnType :Type) : org.abs_models.crowbar.data.Stmt{
    val calleeExpr = translateABSExpToSymExpr(syncCall.callee, returnType)
    val callExpr = translateABSExpToSymExpr(syncCall, returnType)

    if(syncCall.callee is ThisExp)
        return SyncCallStmt(loc, calleeExpr, callExpr as SyncCallExpr)

    val fut = FreshGenerator.getFreshProgVar(type,true)
    val callStmt = CallStmt(fut, calleeExpr, callExpr as CallExpr)
    val syncStmt = SyncStmt(loc, readFut(fut))
    return SeqStmt(callStmt, syncStmt)
}

fun translateABSGuardToSymExpr(input: Guard, returnType: Type) : Expr =
    when(input){
        is ExpGuard -> translateABSExpToSymExpr(input.pureExp, returnType)
        is AndGuard -> SExpr("&&",listOf(translateABSGuardToSymExpr(input.left, returnType), translateABSGuardToSymExpr(input.right, returnType)))
        is ClaimGuard -> {
            val placeholder = SExpr("=",listOf(Const("1"), Const("1"))) //todo: proper translation
            placeholder.absExp = input.`var` // Save reference to original guard expression
            placeholder
        }
        else -> throw Exception("Translation of ${input::class} not supported" )
    }

fun translateABSPatternToSymExpr(pattern : Pattern, overrideType : Type, returnType:Type) : Expr =
    when (pattern) {
        is PatternVarUse -> ProgVar(pattern.name, pattern.type.qualifiedName, pattern.type)
        is PatternVar -> ProgVar(pattern.`var`.name, pattern.type.qualifiedName, pattern.type)
        is LiteralPattern -> translateABSExpToSymExpr(pattern.literal, returnType)
        is UnderscorePattern ->  FreshGenerator.getFreshProgVar(overrideType)
        is ConstructorPattern -> DataTypeExpr(typeWithModule(pattern.constructor, pattern.moduleDecl.name),pattern.type.qualifiedName,pattern.type,pattern.params.map { translateABSPatternToSymExpr(it,it.inhType, returnType) })
        else -> throw Exception("Translation of complex constructors is not supported")
        }

fun typeWithModule(type : String, moduleName : String) :String {
    var constructor = type
    if(!constructor.startsWith("$moduleName."))
        constructor =  "$moduleName.$type"
    return constructor
}

fun filterAtomic(input: Stmt?, app : (Stmt) -> Boolean) : Set<Stmt> {
    if(input == null) return emptySet()
    return when(input){
        is Block ->     input.stmts.fold(emptySet() , { acc, nx -> acc + filterAtomic(nx, app) })
        is WhileStmt -> filterAtomic(input.body, app)
        is IfStmt ->    filterAtomic(input.then, app) +filterAtomic(input.`else`, app)
        else -> if(app(input)) setOf(input) else emptySet()
    }
}


fun directSafe(exp: Exp, safeCalls: List<MethodSig>, safeSyncs: MutableList<VarOrFieldDecl>) : Boolean =
    when(exp) {
        is GetExp       -> exp.pureExp is VarOrFieldUse && safeSyncs.contains((exp.pureExp as VarOrFieldUse).decl)
        is NewExp       -> true
        is AsyncCall    -> safeCalls.contains(exp.methodSig)
        else -> true
    }


fun directSafeGuard(guard: Guard, safeSyncs: MutableList<VarOrFieldDecl>) : Boolean =
    when(guard) {
        is ClaimGuard -> (guard.`var` is VarOrFieldUse) && safeSyncs.contains((guard.`var` as VarOrFieldUse).decl)
        is AndGuard ->  directSafeGuard(guard.left,safeSyncs) && directSafeGuard(guard.right,safeSyncs)
        is DurationGuard ->  true
        else ->  false
    }


fun directlySafe(input: Stmt?, safeCalls: List<MethodSig>, safeSyncs: MutableList<VarOrFieldDecl>) : Boolean {
    if(input == null) return true
    when(input){
        is org.abs_models.frontend.ast.SkipStmt -> return true
        is ExpressionStmt -> return directSafe(input.exp, safeCalls, safeSyncs)
        is VarDeclStmt -> {
            val res = directSafe(input.varDecl.initExp, safeCalls, safeSyncs)
            if(res) safeSyncs.add(input.varDecl)
            return res
        }
        is AssignStmt -> {
            val res = directSafe(input.valueNoTransform, safeCalls, safeSyncs)
            safeSyncs.remove(input.varNoTransform.decl)
            if(res) safeSyncs.add(input.varNoTransform.decl)
            return res
        }
        is Block -> {
            for(stmt in input.stmts){
                val res = directlySafe(stmt, safeCalls, safeSyncs)
                if(!res) return false
            }
            return true
        }

        is WhileStmt -> {
            return directlySafe(input.body, safeCalls, safeSyncs)
        }
        is AwaitStmt -> {
            return directSafeGuard(input.guard, safeSyncs)
        }
        is ReturnStmt -> return directSafe(input.retExp, safeCalls, safeSyncs)
        is IfStmt -> {
            val left = mutableListOf<VarOrFieldDecl>()
            val right = mutableListOf<VarOrFieldDecl>()
            left.addAll(safeSyncs)
            right.addAll(safeSyncs)
            val res = directlySafe(input.then, safeCalls, left) && directlySafe(input.`else`, safeCalls, right)
            safeSyncs.removeAll { true }
            safeSyncs.addAll(left.intersect(right))
            return res
        }
        else -> throw Exception("Analysis of ${input::class} not supported" )
    }
}