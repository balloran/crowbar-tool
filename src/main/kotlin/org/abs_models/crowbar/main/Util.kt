package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.data.Stmt
import org.abs_models.crowbar.interfaces.*
import org.abs_models.crowbar.investigator.CounterexampleGenerator
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.StaticNode
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.tree.getStrategy
import org.abs_models.crowbar.executions.AbstractEvaluation
import org.abs_models.crowbar.types.AbstractType
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.Type
import java.io.File
import java.nio.file.Path
import kotlin.reflect.KClass
import kotlin.reflect.full.companionObject
import kotlin.reflect.full.memberFunctions
import kotlin.system.exitProcess

/*
A number of utility functions for user interaction and proof setup
 */
fun output(text : String, level : Verbosity = Verbosity.NORMAL){
    if(verbosity >= level)
        println(text)
}

/*
Loads an ABS model and returns the AST and the initialized repository.
 */
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
    FunctionRepos.init(model)
    ADTRepos.init(model)
    repos.populateClassReqs(model)
    repos.populateMethodReqs(model)

    // Only useful for AbstractExecution
    repos.populateAbstractReqs(model)

    return Pair(model, repos)
}


/***************************
 The following functions extract some specification from the AST.
 We only consider formulas as specification, other specifications do not need inheritance and can be directly retrieved.
 ****************************/
fun extractInheritedSpec(iDecl : InterfaceTypeUse, expectedSpec : String, mSig: MethodSig, default:Formula) : Formula? {
    for( miSig in iDecl.decl.findChildren(MethodSig::class.java))
        if(miSig.matches(mSig)) return extractSpec(miSig, expectedSpec,mSig.type, default)

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

fun extractMainTotalSpec(mainblock: MainBlock) : MutableMap<Location, AELocSet>{
    val abstractLocations = mutableSetOf<Location>()
    val disjoints = mutableSetOf<Set<Location>>()
    var postcond : AEPhi = AETrue

    var spec : AESpec

    for(annotation in mainblock.nodeAnnotations){
        if(annotation.type.isStringType){
            try {
                spec = AbstractParser.parse((annotation.value as StringLiteral).content)
            }
            catch (e : Exception) {
                output("Exception in string annotation parsing, continuing: ${e.message}")
                continue
            }

            when(spec){
                is AELocDec         -> {
                    abstractLocations.addAll(spec.terms.map { term -> AELocation(term.getName()) })
                }
                is AEDis            ->{
                    disjoints.add(spec.terms.map { term -> AELocation(term.getName()) }.toSet())
                }
                is AEForDec         -> {
                    // Formula declaration are ignored for now
                    continue
                }
                is AEMut            -> {
                    // Mutex declaration is ignored for now
                    continue
                }
                is AENormBehavior   -> {
                    postcond = spec.phi
                }
            }
        }
    }
    abstractLocations.add(AELocation("everything"))

    val concreteLocations = extractLocation(mainblock)

    // On long term the empty list would contain the fields...
    val fullLocations = abstractLocations + concreteLocations
    val fullDisjoints = disjoints + extractDisjoint(mainblock, concreteLocations, emptyList())


    val ret: MutableMap<Location, AELocSet> = mutableMapOf()
    for(location in abstractLocations){
        ret[location] = AELocSet(fullLocations.map { loc -> Pair(false, loc) })
    }
    for(location in concreteLocations){
        ret[location] = AELocSet(abstractLocations.map { loc -> Pair(false, loc) })
    }

    val typeMap : Map<Location, Type> = (concreteLocations.map { loc ->
        if (loc is ProgVar) {
            Pair(loc, loc.concrType)
        } else if (loc is Field) Pair(loc, loc.concrType)
        else throw Exception("abstract location in concrete location list")
    }).toMap()

    //output("$typeMap")

    for(disjoint in fullDisjoints){
        //output("$disjoint")
        val newDisjoint = disjoint.map { loc ->
            if (abstractLocations.contains(loc)) {
                loc
            } else {
                ProgVar(loc.name, typeMap[ProgVar(loc.name)]!!)
            }
        }

        for(location in newDisjoint){
            val locSet = ret[location]!!.locs.toMutableList()
            locSet.removeAll(newDisjoint.map{ loc -> Pair(false, loc)})
            ret[location] = AELocSet(locSet)
        }

    }

    return ret
}

fun<T: ASTNode<out ASTNode<*>>?> extractGlobalSpec(mainblock: ASTNode<T>) : Pair<MutableMap<Location, AELocSet>, Formula>{
    val ret = mutableMapOf<Location, AELocSet>()

    val locations = mutableSetOf<Location>()
    val disjoints = mutableSetOf<List<Location>>()
    var postcond : AEPhi = AETrue

    var spec : AESpec

    for(annotation in mainblock.nodeAnnotations){
        if(annotation.type.isStringType){
            try {
                spec = AbstractParser.parse((annotation.value as StringLiteral).content)
            }
            catch (e : Exception) {
                output("Exception in string annotation parsing, continuing: ${e.message}")
                continue
            }

            when(spec){
                is AELocDec         -> {
                    locations.addAll(spec.terms.map { term -> AELocation(term.getName()) })
                }
                is AEDis            ->{
                    disjoints.add(spec.terms.map { term -> AELocation(term.getName()) })
                }
                is AEForDec         -> {
                    // Formula declaration are ignored for now
                    continue
                }
                is AEMut            -> {
                    // Mutex declaration is ignored for now
                    continue
                }
                is AENormBehavior   -> {
                    postcond = spec.phi
                }
            }
        }
    }
    locations.add(AELocation("everything"))

    for(location in locations){
        ret[location] = AELocSet(locations.map{ loc -> Pair(false, loc) }.filter { it.second != location })
    }

    for(disjoint in disjoints){

        // Identify concrete locations in disjoint.
        val newDisjoint = disjoint.map { loc ->
            if (locations.contains(loc)) {
                loc
            } else {
                ProgVar((loc as AELocation).name)
            }
        }

        for(location in newDisjoint){
            // The location has already been seen, just update its AELocSet
            if(ret.containsKey(location)){
                val locSet = ret[location]!!.locs.toMutableList()
                locSet.removeAll(disjoint.map{ loc -> Pair(false, loc)})
                ret[location] = AELocSet(locSet)
            }
            // The location has never been seen this has to be a concrete location.
            else {
                // Create the set of all Abstract locations, the filter is overkill.
                val locSet = locations.filterIsInstance<AELocation>().map { loc -> Pair(false, loc) }.toMutableList()

                // Update the set of all Abstract locations, according to the disjoint.
                locSet.removeAll(disjoint.map { loc -> Pair(false, loc) }.toSet())

                // Add the concrete location ot the map.
                ret[location] = AELocSet(locSet)

                // Add the concrete location to every location that is not in disjoint
                for (loc in locations) {
                    if (!disjoint.contains(loc)) {
                        val newLocSet = ret[loc]!!.locs.toMutableList()
                        newLocSet.add(Pair(false, location))
                        ret[loc] = AELocSet((newLocSet))
                    }
                }
            }
        }
    }

    /*
    for(location in ret.keys){
        output("${location.prettyPrint()} ${ret[location]!!.prettyPrint()}")
    }
    */

    return Pair(ret, exprToForm(translatePhi(postcond, emptyMap())))

}

fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, returnType: Type, default:Formula = True, multipleAllowed:Boolean = true) : Formula {
    var ret : Formula? = null
    if(decl is FunctionDecl){
        for(annotation in decl.annotationList){
            if(!annotation.type.toString().endsWith(".Spec")) continue
            if(annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $decl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if(annotated.constructor != expectedSpec) continue
            val next = exprToForm(translateExpression(annotated.getParam(0) as Exp,decl.type, emptyMap()))
            ret = if(ret == null) next else And(ret, next)
            if(!multipleAllowed) break
        }
    }else if (decl is MethodImpl){
        ret = extractInheritedSpec(decl.methodSig,expectedSpec, default)
    }else {
        for (annotation in decl.nodeAnnotations){
            if(!annotation.type.toString().endsWith(".Spec")) continue
            if(annotation.value !is DataConstructorExp) {
                throw Exception("Could not extract any specification from $decl because of the expected value")
            }
            val annotated = annotation.value as DataConstructorExp
            if(annotated.constructor != expectedSpec) continue
            val next = exprToForm(translateExpression(annotated.getParam(0) as Exp,returnType, emptyMap()))
            ret = if(ret == null) next else And(ret, next)
            if(!multipleAllowed) break
        }
    }

    if(ret == null) {
        ret = default
        if(verbosity >= Verbosity.VVV)
            println("Crowbar-v: Could not extract $expectedSpec specification, using ${default.prettyPrint()}")
    }

    return ret
}

fun extractRoleSpec(classDecl: ClassDecl): Formula {
    return classDecl.annotations.filter {
        it.type.toString()
            .endsWith(".Spec") && it.value is DataConstructorExp && (it.value as DataConstructorExp).constructor == "Role"
    }.map {
        val roleAnnotation = it.value as DataConstructorExp

        if (roleAnnotation.getParam(0) !is StringLiteral)
            throw Exception("First argument of Role annotation should be role name as string")
        if (roleAnnotation.getParam(1) !is FieldUse)
            throw Exception("Second argument of Role annotation should be a field use")

        val roleString = (roleAnnotation.getParam(0) as StringLiteral).content
        val fieldUse = (roleAnnotation.getParam(1) as FieldUse)
        val field = Field(fieldUse.name + "_f", fieldUse.type)
        Predicate("hasRole", listOf(exprToTerm(field), Function("\"$roleString\"")))
    }.fold(True as Formula) { acc, elem -> And(acc, elem) }
}





/***************************
Utility to extract
 ****************************/
fun Model.extractAllClasses() : List<ClassDecl> =
     this.moduleDecls.filter { !it.name.startsWith("ABS.") }
                     .map { it.decls.filterIsInstance<ClassDecl>() }
                     .foldRight(emptyList()) { a, b -> a + b }

fun Model.extractFunctionDecl(moduleName: String, funcName: String) : FunctionDecl {
    val moduleDecl = moduleDecls.firstOrNull { it.name == moduleName }
    if(moduleDecl == null){
        System.err.println("module not found: $moduleName")
        exitProcess(-1)
    }
    val funcDecl : FunctionDecl? = moduleDecl.decls.firstOrNull { it is FunctionDecl && it.name == funcName } as FunctionDecl?
    if(funcDecl == null){
        System.err.println("function not found: ${moduleName}.$funcName")
        exitProcess(-1)
    }
    return funcDecl
}

fun Model.extractClassDecl(moduleName: String, className: String) : ClassDecl {
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

    return classDecl
}

fun FunctionDecl.extractFunctionNode(usedType: KClass<out DeductType>) : SymbolicNode{
    val callTarget = usedType.memberFunctions.first { it.name == "extractFunctionNode" }
    val obj = usedType.companionObject!!.objectInstance
    return callTarget.call(obj, this) as SymbolicNode
}
fun Model.extractMainNode(usedType: KClass<out DeductType>) : SymbolicNode{
    val callTarget = usedType.memberFunctions.first { it.name == "extractMainNode" }
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




/***************************
Utility to start the symbolic execution
 ****************************/
var count = 0
fun executeNode(node : SymbolicNode, repos: Repository, usedType: KClass<out DeductType>, identifier: String = "unknown", classdecl : String = "") : Boolean{
    output("Crowbar  : starting symbolic execution....")
    val pit = getStrategy(usedType,repos, classdecl)
    pit.execute(node)


    for(key in repos.classFrames.keys){
        repos.classFrames[key]?.set(AELocation("nothing"), AELocSet(emptyList()))
    }

    //output("\n${repos.classFrames}\n")

    output("Crowbar-v: symbolic execution tree:",Verbosity.V)
    output(node.debugString(0),Verbosity.V)

    //output("$node")

    if(!node.finishedExecution()){
        System.err.println("could not finish symbolic execution")
        println(node.debugString(0))
        exitProcess(-1)
    }

    output("Crowbar  : closing open branches....")

    val maps = mutableListOf<Map<Location, Term>>()

    var closed = true
    for(l in node.collectLeaves()){
        when (l) {
            is LogicNode -> {
                if(usedType.isInstance(AbstractType)){
                    if(true){
                        val exec = AbstractEvaluation(repos.classFrames[classdecl]!!)
                        closed = exec.evaluate(l) && closed
                        maps.add(exec.substMap)
                        exec.printRawSubstMap()
                    }
                    else if(false){
                        framing = repos.classFrames[classdecl]!!
                        output("Crowbar-v: "+ deupdatify(l.ante).prettyPrint()+"->"+deupdatify(l.succ).prettyPrint(), Verbosity.V)
                        closed = closed && l.evaluate()
                    }
                    count++
                }
                else{
                    output("Crowbar-v: "+ deupdatify(l.ante).prettyPrint()+"->"+deupdatify(l.succ).prettyPrint(), Verbosity.V)
                    closed = closed && l.evaluate()
                    count++
                }
            }
            is StaticNode -> {
                output("Crowbar: open static leaf ${l.str}", Verbosity.SILENT)
            }
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


/***************************
General utility
 ****************************/
fun normalize(st : Stmt) : Stmt =
    when(st){
        is SeqStmt ->
            when(st.first){
                is SeqStmt -> normalize(SeqStmt(st.first.first,SeqStmt(st.first.second,st.second)))
                else -> SeqStmt(st.first, normalize(st.second))
            }
        else -> st
    }

fun getDeclaration(mSig: MethodSig, cDecl : ClassDecl): InterfaceDecl? =
     cDecl.implementedInterfaceUses.map{ getIDeclaration(mSig, it.decl as InterfaceDecl) }.firstOrNull()

fun getIDeclaration(mSig: MethodSig, iDecl : InterfaceDecl): InterfaceDecl?{
    for(mDecl in iDecl.allMethodSigs){
        if(mDecl.matches(mSig)) return iDecl
    }
    return iDecl.extendedInterfaceUseList.map{ getIDeclaration(mSig, it.decl as InterfaceDecl) }.firstOrNull()
}