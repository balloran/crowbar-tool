package org.abs_models.crowbar.executions

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.interfaces.*
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.tree.*
import org.abs_models.crowbar.types.AbstractType
import org.abs_models.crowbar.types.booleanFunction
import org.abs_models.frontend.ast.Model
import org.abs_models.frontend.typechecker.DataTypeType
import java.nio.file.Path

class FullRelationExecution(private val filePaths: List<Path>){

    private val setNodes: MutableSet<RelationalNode> = filePaths.map { val aux = load(listOf(it)); RelationalNode(aux.first, aux.second, filePaths.indexOf(it)) }.toMutableSet()

    private var maxIndex = setNodes.size

    private val setRelations = mutableSetOf<Pair<Int, Int>>()

    init {
        initRelations()
    }

    fun execute(){

        output("Crowbar : Start of node execution.")

        while(!execIsFinished()){
            executeOneStep()
        }

        output("Crowbar : End of node execution.")

        output("Crowbar : Start of node evaluation.")

        setNodes.forEach { it.evaluate() }

        output("Crowbar : End of node evaluation.")

        output("Crowbar : Start of map comparison.")

        for(relation in setRelations){
            compareMap(relation)
        }

        output("Crowbar : End of map comparison.")
    }

    private fun executeOneStep(){
        val currentNode = setNodes.first(){!it.finished}
        val children = currentNode.executeOneStep().filter { it is SymbolicNode || it is LogicNode }

        if(children.size == 1){
            if(children[0] is SymbolicNode)
                setNodes.filter { it.index == currentNode.index }.forEach { it.node = children[0] as SymbolicNode }
            else {
                setNodes.filter { it.index == currentNode.index }.forEach {
                    it.finishedVal = children[0] as LogicNode
                    it.finished = true
                }
            }
        }
        else if (children.size > 1){
            setNodes.remove(currentNode)
            val relationCurrentNode = setRelations.filter { it.first == currentNode.index || it.second == currentNode.index }.toSet()
            setRelations.removeAll(relationCurrentNode)
            for(node in children){
                if(node is SymbolicNode){
                    val aux = RelationalNode(currentNode.model, currentNode.repos, maxIndex)
                    aux.node = node
                    setNodes.add(aux)
                    maxIndex++

                    for(relation in relationCurrentNode){
                        if(relation.first == currentNode.index){
                            setRelations.add(Pair(aux.index, relation.second))
                        }
                        else{
                            setRelations.add(Pair(relation.first, aux.index))
                        }
                    }
                }
            }

        }
        else{
            throw Exception("No return from the rules.")
        }
    }

    private fun execIsFinished() : Boolean {
        return setNodes.fold(true ){acc, node -> acc && node.finished}
    }

    private fun initRelations(){
        val max = filePaths.size
        for(i in 0 until max){
            for (j in 0 until i){
                setRelations.add(Pair(j, i))
            }
        }
    }

    private fun compareMap(relation : Pair<Int, Int>){
        val node1 = setNodes.first { it.index == relation.first }
        val node2 = setNodes.first { it.index == relation.second }

        val sharedKeys = node1.valueMap.keys.intersect(node2.valueMap.keys)

        if(sharedKeys != node1.valueMap.keys || sharedKeys != node2.valueMap.keys){
            output("Crowbar: warning not the same set of locations, performing the comparison on the following locations only: $sharedKeys")
        }

        val map1 = node1.valueMap.filterKeys { it in sharedKeys && it is ConcreteLocation }
        val map2 = node2.valueMap.filterKeys { it in sharedKeys && it is ConcreteLocation }

        //val map1 = node1.valueMap.filterKeys { it in sharedKeys }
        //val map2 = node2.valueMap.filterKeys { it in sharedKeys }

        val aux = generateSMT(listOf(map1, map2), listOf(node1.precond, node2.precond))

        //output("$aux")

        val res = evaluateSMT(aux)

        if(!res)
            output("$aux")

        output("Crowbar : Result of map comparisons: $res")
    }

    private fun generateSMT(dataMaps : List<Map<Location, Term>>, dataPres : List<LogicElement>) : String{

        val allTerms = (dataMaps.map { it.values }.flatten().map { it.iterate { true } } + dataPres.map { pre -> pre.iterate { true } }).flatten().toSet()

        resetWildCards()
        val fields = allTerms.filterIsInstance<Field>()

        ADTRepos.setUsedHeaps(fields.map { ADTRepos.libPrefix(it.concrType.qualifiedName) }.toSet())

        (allTerms.filter { it is DataTypeConst && isConcreteGeneric(it.concrType!!) }.toSet() as Set<DataTypeConst>).map {
            ADTRepos.addGeneric(it.concrType!! as DataTypeType)
        }

        val vars = allTerms.filterIsInstance<ProgVar>().filter { it.name != "heap" && it.name !in specialHeapKeywords }
        val heaps = allTerms.filterIsInstance<org.abs_models.crowbar.data.Function>().filter { it.name.startsWith("NEW") }
        val funcs = allTerms.filterIsInstance<org.abs_models.crowbar.data.Function>().filter { it.name.startsWith("f_") }
        val fullAbs = allTerms.filterIsInstance<FullAbstractTerm>()
        val partAbs = allTerms.filterIsInstance<PartialAbstractTerm>()
        val poatAbs = allTerms.filterIsInstance<PreciseOnAbstractTerm>()
        val unknowns = allTerms.filterIsInstance<UnknownTerm>()
        val absExp = allTerms.filterIsInstance<AbstractFormula>()

        val presSMT = dataPres.joinToString ("\n"){ "(assert ${it.toSMT()}  )" }

        val andEqualities = dataMaps[0].keys.joinToString ("\n\t"){ key -> "(and ( = " + dataMaps.joinToString ( " " ){ it[key]!!.toSMT() } + ")" }
        val closeEqualities = dataMaps[0].keys.joinToString ( "\n\t" ){")"}
        val equalities = "(assert (not $andEqualities $closeEqualities ) )"

        //output(equalities)

        val functionDecl = FunctionRepos.toString()
        val primitiveTypesDecl = ADTRepos.primitiveDtypesDecl.filter{!it.type.isStringType}.joinToString("\n\t") { "(declare-sort ${it.qualifiedName} 0)" }
        val wildcards: String = wildCardsConst.map { FunctionDeclSMT(it.key,it.value).toSMT("\n\t") }.joinToString("") { it }
        val fieldsDecl = fields.joinToString("\n\t"){ "(declare-const ${it.name} Field)\n" +
                if(it.concrType.isInterfaceType)
                    "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                else ""}
        val varsDecl = vars.joinToString("\n\t"){"(declare-const ${it.name} ${
            if(it.concrType.isUnknownType)
                throw Exception("Var with unknown type: ${it.name}")
            else if (isConcreteGeneric(it.concrType) && !it.concrType.isFutureType) {
                ADTRepos.addGeneric(it.concrType as DataTypeType)
                genericTypeSMTName(it.concrType)
            }
            else
                ADTRepos.libPrefix(it.concrType.qualifiedName)
        })\n" +
                if(it.concrType.isInterfaceType)
                    "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                else ""
        }

        val fullAbsDecl = (fullAbs.map{ "(declare-fun AEFull_${it.name.name} (Int Int ${
            it.accessibleValues.joinToString(" ") { term ->
                typeOfConcreteTermToSMT(term)
            }
        }) ${
            typeOfAbstractToSMT(it.concrType, it.name.name)
        })\n" }.toSet() +
                fullAbs.map {
                    if (it.concrType.isInterfaceType)
                        "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                    else ""
                }.toSet().filter { it != "" }).joinToString("\n\t") { it }

        //output("$fullAbs")
        //output("$partAbs")

        val partAbsDecl = (partAbs.map { "(declare-fun AEPartial_${it.name.name} (Int Int ${
            it.accessibleValues.joinToString(" ") { term ->
                typeOfConcreteTermToSMT(term)
            }
        } ${
            typeOfAbstractToSMT(it.concrType, it.name.name)
        }) ${
            typeOfAbstractToSMT(it.concrType, it.name.name)
        })\n" }.toSet() +
                partAbs.map {
                    if (it.concrType.isInterfaceType)
                        "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                    else ""
                }.toSet().filter { it != "" }).joinToString("\n\t") { it }

        val poatAbsDecl = poatAbs.map{ precise ->
            val orderedKeys = precise.updates.keys.sortedBy { it.hashCode() }
            "(declare-fun POAT_${
                orderedKeys.joinToString("_") { it.name }
            } (${
                orderedKeys.joinToString(" ") { typeOfConcreteTermToSMT(precise.updates[it]!!) }
            } ${
                typeOfConcreteTermToSMT(precise.abstract)
            }) ${
                typeOfConcreteTermToSMT(precise.abstract)
            })"
        }.toSet().joinToString ("\n\t"){ it }

        val unknownsDecl = unknowns.map {
            "(declare-const ${it.toSMT()} ${typeOfLocation(it.target)})"
        }.toSet().joinToString("\n\t") { it }

        val absExpDecl = absExp.joinToString("\n\t") { "(declare-const ${it.toSMT() } ${
            if(it.concrType.isUnknownType)
                throw Exception("Var with unknown type: ${it.name}")
            else if (isConcreteGeneric(it.concrType) && !it.concrType.isFutureType) {
                ADTRepos.addGeneric(it.concrType as DataTypeType)
                genericTypeSMTName(it.concrType)
            }
            else
                ADTRepos.libPrefix(it.concrType.qualifiedName)
        })\n" +
                if(it.concrType.isInterfaceType)
                    "(assert (implements ${it.name} ${it.concrType.qualifiedName}))\n\t"
                else ""}

        val objectImpl = heaps.joinToString("\n"){
                x: Function ->
            if(x.name in ADTRepos.objects)
                ADTRepos.objects[x.name]!!.types.joinToString("\n\t") {
                    "(assert (implements " +
                            if(x.params.isNotEmpty()){
                                "(${x.name} " +
                                        x.params.joinToString (" "){term -> term.toSMT()} +
                                        ")  ${it.qualifiedName}))"}
                            else{
                                "${x.name} ${it.qualifiedName}))"
                            }

                }else ""

        }
        val objectsDecl = heaps.joinToString("\n\t"){"(declare-fun ${it.name} (${it.params.joinToString (" "){
                term ->
            if(term is DataTypeConst) {
                ADTRepos.addGeneric(term.concrType!! as DataTypeType)
                genericTypeSMTName(term.concrType)
            }
            else if(term is Function && term.name in booleanFunction) "Bool"
            else { "Int"
            }
        }}) Int)"

        }
        val funcsDecl = funcs.joinToString("\n") { "(declare-const ${it.name} Int)"}
        var fieldsConstraints = ""
        fields.forEach { f1 -> fields.minus(f1).forEach{ f2 -> if(ADTRepos.libPrefix(f1.concrType.qualifiedName) == ADTRepos.libPrefix(
                f2.concrType.qualifiedName
            )
        ) fieldsConstraints += "(assert (not ${Eq(f1,f2).toSMT()}))" } } //??

        return """
;header
    $smtHeader
;primitive type declaration
    $primitiveTypesDecl
;valueOf
    $valueOf
;data type declaration
    ${ADTRepos.dTypesToSMT()}

;interface type declaration
    (declare-fun   implements (ABS.StdLib.Int Interface) Bool)
    (declare-fun   extends (Interface Interface) Bool)
    (assert (forall ((i1 Interface) (i2 Interface) (i3 Interface))
     (=> (and (extends i1 i2) (extends i2 i3))
      (extends i1 i3))))
      
    (assert (forall ((i1 Interface) (i2 Interface) (object ABS.StdLib.Int))
     (=> (and (extends i1 i2) (implements object i1))
      (implements object i2))))
      
      ${ADTRepos.interfaceExtendsToSMT()}
      
;generics declaration
    ${ADTRepos.genericsToSMT()}
;heaps declaration
    ${ADTRepos.heapsToSMT()}
;wildcards declaration
    $wildcards
;functions declaration
    $functionDecl
;generic functions declaration :to be implemented and added
;    
;fields declaration
    $fieldsDecl
;variables declaration
    $varsDecl
;abstract constants declaration
    $fullAbsDecl
    $partAbsDecl
    $poatAbsDecl
;abstract expression declaration
    $absExpDecl
;unknowns constants declaration
    $unknownsDecl
;objects declaration
    $objectsDecl
    
;objects interface declaration
    $objectImpl
;funcs declaration
    $funcsDecl
;fields constraints
    $fieldsConstraints
    ; Preconditions
    $presSMT
    ; Negated equalities
    $equalities
    (check-sat)
    (exit)
    """.trimIndent()

    }
}

class RelationalNode(val model  : Model, val repos : Repository, val index : Int){

    private val nodeStrategy = getStrategy(AbstractType::class, repos, "main") as DefaultStrategy
    var node = model.extractMainNode(AbstractType::class)
    lateinit var finishedVal : LogicNode
    var finished = false
    var valueMap : MutableMap<Location, Term> = mutableMapOf()
    lateinit var precond : LogicElement

    fun executeOneStep() : List<SymbolicTree> {
        for(rule in nodeStrategy.rules){
            if(rule.isApplicable(node.content)){
                val next = rule.apply(node.content)
                if(next != null){
                    if(node.info is LeafInfo){
                        println("Prop "+ node.info)
                        next.forEach { if(it.info is NoInfo) it.info = node.info }
                    }
                }
                if(next == null)
                    return emptyList()
                return next
            }
        }
        throw Exception("No applicable rule")
    }

    fun evaluate(){
        val framing = repos.classFrames["main"]!!
        val exec = AbstractEvaluation(framing)
        val res = exec.evaluateAndPrecond(finishedVal)
        precond = res.second
        valueMap = exec.substMap
        exec.printSubstMap()

        if(!res.first){
            output("Crowbar: unverified postcondition : $finishedVal")
        }
        else{
            output("Crowbar : verified postcondition.")
        }
    }
}