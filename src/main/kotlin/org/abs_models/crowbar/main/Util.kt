package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.interfaces.translateABSExpToSymExpr
import org.abs_models.crowbar.investigator.CounterexampleGenerator
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.StaticNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.getStrategy
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.Type
import sun.reflect.generics.tree.ReturnType
import java.io.File
import java.nio.file.Path
import kotlin.reflect.KClass
import kotlin.reflect.full.companionObject
import kotlin.reflect.full.memberFunctions
import kotlin.system.exitProcess


fun output(text : String, level : Verbosity = Verbosity.NORMAL){
    if(verbosity >= level)
        println(text)
}

fun load(paths : List<Path>) : Pair<Model,Repository> {

    output("Crowbar  : loading files....")
    val input = paths.map{ File(it.toString()) }
    if(input.any { !it.exists() }) {
        System.err.println("file not found: $paths")
        exitProcess(-1)
    }

    output("Crowbar  : loading ABS model....")
    val model = try {
        org.abs_models.frontend.parser.Main().parse(input)
    } catch (e : Exception) {
        e.printStackTrace()
        System.err.println("error during parsing, aborting")
        exitProcess(-1)
    }
    if(model.hasTypeErrors())
        throw Exception("Compilation failed with type errors")

    val repos = Repository(model)


    //initialization: first read the types, then the function definitions and then the specifications
    FunctionRepos.init(model, repos)
    ADTRepos.init(model)
    repos.populateClassReqs(model)
    repos.populateMethodReqs(model)
    return Pair(model, repos)
}

fun extractInheritedSpec(iDecl : InterfaceTypeUse, expectedSpec : String, mSig: MethodSig, default:Formula) : Formula? {
    for( miSig in iDecl.decl.findChildren(MethodSig::class.java)){
        if(miSig.matches(mSig)) return extractSpec(miSig, expectedSpec,mSig.type, default)
    }
    if(iDecl.decl.getChild(1) !is org.abs_models.frontend.ast.List<*>) throw Exception("Invalid specification AST ${iDecl.decl}")

    @Suppress("UNCHECKED_CAST")
    val uses = iDecl.decl.getChild(1) as org.abs_models.frontend.ast.List<InterfaceTypeUse>
    for(use in uses){
        val next = extractInheritedSpec(use, expectedSpec, mSig, default)
        if(next != null) return next
    }
    return null
}

fun extractInheritedSpec(mSig : MethodSig, expectedSpec : String, default:Formula = True) : Formula {
    val direct = extractSpec(mSig, expectedSpec, mSig.type,default)
    val conDecl = mSig.contextDecl
    if(conDecl is ClassDecl){
        for( iDecl in conDecl.implementedInterfaceUses){
            val next = extractInheritedSpec(iDecl, expectedSpec, mSig, default)
            if(next != null) return And(direct,next)
        }
    }
    return direct
}

fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, returnType: Type, default:Formula = True, multipleAllowed:Boolean = true) : Formula {
    var ret : Formula? = null
    //TODO: this seems to be a problem with annotations in the functional layer in the ABS AST
    //TODO: refactor the code duplication
    if(decl is FunctionDecl){
        for(annotation in decl.annotationList){
            if(!annotation.type.toString().endsWith(".Spec")) continue
            if(annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $decl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if(annotated.constructor != expectedSpec) continue
            val next = exprToForm(translateABSExpToSymExpr(annotated.getParam(0) as Exp,decl.type))
            ret = if(ret == null) next else And(ret, next)
            if(!multipleAllowed) break
        }
    }else if (decl is MethodImpl && decl !is FunctionDecl){
        ret = extractInheritedSpec(decl.methodSig,expectedSpec, default)
    }else {
        for (annotation in decl.nodeAnnotations){
            if(!annotation.type.toString().endsWith(".Spec")) continue
            if(annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $decl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if(annotated.constructor != expectedSpec) continue
            val next = exprToForm(translateABSExpToSymExpr(annotated.getParam(0) as Exp,returnType))
            ret = if(ret == null) next else And(ret, next)
            if(!multipleAllowed) break
        }
    }
    if(ret == null) {
        ret = default
        if(verbosity >= Verbosity.VVV)
            println("Crowbar-v: Could not extract $expectedSpec specification, using ${default.prettyPrint()}")
    }
    return specialKeyHeapExtract(ret) as Formula //Todo: add warning for old and last in precondition
}


fun Model.extractAllClasses() : List<ClassDecl>{
    var l = emptyList<ClassDecl>()
    for( module in this.moduleDecls){
        if(module.name.startsWith("ABS.")) continue
        for( decl in module.decls){
            if(decl is ClassDecl)
                l = l + decl
        }
    }
    return l
}

fun Model.extractFunctionDecl(moduleName : String, funcName : String, repos : Repository) : FunctionDecl {
    val moduleDecl = moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val funcDecl : FunctionDecl? = moduleDecl.decls.firstOrNull { it is FunctionDecl && it.name == funcName } as FunctionDecl?
    if(funcDecl == null){
        System.err.println("function not found: ${moduleName}.${funcDecl}")
        exitProcess(-1)
    }

    if(    funcDecl.params.any { !repos.isAllowedType(it.type.toString()) }
        ||  !repos.isAllowedType(funcDecl.type.toString())  ){
        System.err.println("parameters and return types with non-Int type not supported")
        exitProcess(-1)
    }
    return funcDecl
}

fun Model.extractClassDecl(moduleName : String, className : String, repos : Repository) : ClassDecl {
    val moduleDecl = moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val classDecl : ClassDecl? = moduleDecl.decls.firstOrNull { it is ClassDecl && it.name == className } as ClassDecl?
    if(classDecl == null){
        System.err.println("class not found: ${moduleName}.${className}")
        exitProcess(-1)
    }

    if(    classDecl.params.any { !repos.isAllowedType(it.type.toString()) }
        || classDecl.fields.any { !repos.isAllowedType(it.type.toString()) } ){
        System.err.println("fields with non-Int type not supported")
        exitProcess(-1)
    }
    return classDecl
}

fun FunctionDecl.exctractFunctionNode(usedType: KClass<out DeductType>) : SymbolicNode{
    val callTarget = usedType.memberFunctions.first { it.name == "exctractFunctionNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}
fun Model.exctractMainNode(usedType: KClass<out DeductType>) : SymbolicNode{
    val callTarget = usedType.memberFunctions.first { it.name == "exctractMainNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}

fun ClassDecl.extractInitialNode(usedType: KClass<out DeductType>) : SymbolicNode {
    val callTarget = usedType.memberFunctions.first { it.name == "extractInitialNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}

fun ClassDecl.extractMethodNode(usedType: KClass<out DeductType>, name : String, repos: Repository) : SymbolicNode {
    val callTarget = usedType.memberFunctions.first { it.name == "extractMethodNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this, name, repos) as SymbolicNode
}

fun executeNode(node : SymbolicNode, repos: Repository, usedType: KClass<out DeductType>, identifier: String = "unknown") : Boolean{ //todo: this should handle inference and static leafs now

    output("Crowbar  : starting symbolic execution....")
    val pit = getStrategy(usedType,repos)
    pit.execute(node)

    output("Crowbar-v: symbolic execution tree:",Verbosity.V)
    output(node.debugString(0),Verbosity.V)

    if(!node.finishedExecution()){
        System.err.println("could not finish symbolic execution")
        println(node.debugString(0))
        exitProcess(-1)
    }

    output("Crowbar  : closing open branches....")
    var closed = true
    for(l in node.collectLeaves()){
        if(l is LogicNode){
            output("Crowbar-v: "+ deupdatify(l.ante).prettyPrint()+"->"+deupdatify(l.succ).prettyPrint(), Verbosity.V)
            closed = closed && l.evaluate()
            output("Crowbar-v: verified? ${l.evaluate()}", Verbosity.V)
        } else if(l is StaticNode){
            output("Crowbar: open static leaf ${l.str}", Verbosity.SILENT)
        } else {
            System.err.println("Crowbar-v: non-logical analysis nodes not supported")
            throw Exception("Crowbar-v: non-logical analysis nodes not supported")
        }

    }

    if(!closed && investigate) {
        output("Crowbar  : failed to close node, starting investigator....")
        CounterexampleGenerator.investigateAll(node, identifier)
    }

    return closed
}

fun ClassDecl.executeAll(repos: Repository, usedType: KClass<out DeductType>): Boolean{
    val iNode = extractInitialNode(usedType)
    var totalClosed = executeNode(iNode, repos, usedType, "<init>")
    output("Crowbar  : Verification <init>: $totalClosed")

    for(m in methods){
        val node = extractMethodNode(usedType, m.methodSig.name, repos)
        val closed = executeNode(node, repos, usedType, m.methodSig.name)
        output("Crowbar  : Verification ${m.methodSig.name}: $closed")
        totalClosed = totalClosed && closed
    }
    return totalClosed
}

fun normalize(st : Stmt) : Stmt {
    return when(st){
        is SeqStmt -> {
            when(st.first){
                is SeqStmt -> {
                    val a = st.first.first
                    val b = st.first.second
                    val c = st.second
                    normalize(SeqStmt(a,SeqStmt(b,c)))
                }
                else -> SeqStmt(st.first, normalize(st.second))
            }
        }
        else -> st
    }
}


fun getDeclaration(mSig: MethodSig, cDecl : ClassDecl): InterfaceDecl? {
    for(iiDecl  in cDecl.implementedInterfaceUses.map{ it.decl }){
        val next = iiDecl as InterfaceDecl
        val ret = getIDeclaration(mSig,next)
        if(ret != null) return ret
    }
    return null
}

fun getIDeclaration(mSig: MethodSig, iDecl : InterfaceDecl): InterfaceDecl?{
    for(mDecl in iDecl.allMethodSigs){
        if(mDecl.matches(mSig)) return iDecl
    }
    for(iiDecl in iDecl.extendedInterfaceUseList){
        val next = iiDecl.decl as InterfaceDecl
        val ret = getIDeclaration(mSig,next)
        if(ret != null) return ret
    }
    return null
}

fun specialKeyHeapExtract(input: LogicElement) : LogicElement {
    return when(input){
        is Function -> {
            if (specialHeapKeywords.containsKey(input.name)){
                if(input.params.size == 1) {
                    return specialKeyHeapExtract(input.params[0], input.name)
                }else
                    throw Exception("Special keyword old must have one argument, actual arguments size:" + input.params.size)
            }
            return Function(input.name, input.params.map { p -> specialKeyHeapExtract(p) as Term })
        }
        is Predicate -> Predicate(input.name, input.params.map { p -> specialKeyHeapExtract(p) as Term })
        is Impl -> Impl(specialKeyHeapExtract(input.left) as Formula, specialKeyHeapExtract(input.right) as Formula)
        is And -> And(specialKeyHeapExtract(input.left) as Formula, specialKeyHeapExtract(input.right) as Formula)
        is Or -> Or(specialKeyHeapExtract(input.left) as Formula, specialKeyHeapExtract(input.right) as Formula)
        is Not -> Not(specialKeyHeapExtract(input.left) as Formula)
        else                -> input
    }
}

fun specialKeyHeapExtract(input: LogicElement, specialHeap : String) : LogicElement {
    return when(input){
        is Function     -> Function(input.name, input.params.map { p -> specialKeyHeapExtract(p,specialHeap) as Term })
        is Predicate    -> Predicate(input.name, input.params.map { p -> specialKeyHeapExtract(p,specialHeap) as Term })
        is Impl -> Impl(specialKeyHeapExtract(input.left,specialHeap) as Formula, specialKeyHeapExtract(input.right,specialHeap) as Formula)
        is And  -> And(specialKeyHeapExtract(input.left,specialHeap) as Formula, specialKeyHeapExtract(input.right,specialHeap) as Formula)
        is Or   -> Or(specialKeyHeapExtract(input.left,specialHeap) as Formula, specialKeyHeapExtract(input.right,specialHeap) as Formula)
        is Not  -> Not(specialKeyHeapExtract(input.left,specialHeap) as Formula)
        is Heap -> {
            if(specialHeapKeywords.containsKey(specialHeap))
                specialHeapKeywords[specialHeap] as LogicElement
            else
                throw Exception("The special heap keyword $specialHeap is not supported")
        }
        else    -> input
    }
}
