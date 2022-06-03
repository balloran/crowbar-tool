package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.interfaces.*
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.Model
import org.abs_models.frontend.typechecker.DataTypeType
import java.nio.file.Path

class RelationExecution (private val filePaths: List<Path>){

    var listModRep: List<Pair<Model, Repository>> = emptyList()

    var currentNodeStrategy = emptyList<Pair<SymbolicNode, Strategy>>()

    init {
        // Load model and reposit
        listModRep = filePaths.map { path -> load(listOf(path)) }
    }

    /**
     * Main execution function for the relational verification, for now it only deals with the main block.
     */
    fun execute(){
        extractMainNodesStrategy()
        executeNodes()
        compareMaps(evaluateNodes())
    }

    /**
     * Extract the main node for each source file.
     */
    private fun extractMainNodesStrategy(){
        currentNodeStrategy = listModRep.map { pair ->
            Pair(
                pair.first.extractMainNode(AbstractType::class),
                getStrategy(AbstractType::class, pair.second, "main")
            )
        }
    }

    /**
     * Execute the nodes in currentNodeStrategy, currently it is a simple execute, it will change.
     */
    private fun executeNodes(){
        currentNodeStrategy.forEach { pair -> pair.second.execute(pair.first) }
    }

    /**
     * Perform the abstract evaluation of the nodes in currentNodeStrategy.
     */
    private fun evaluateNodes() : List<List<Pair<Map<Location, Term>, LogicElement>>>{

        output("Crowbar: start of abstract evaluation.")

        val listMaps: MutableList<MutableList<Pair<MutableMap<Location, Term>, LogicElement>>> = mutableListOf()
        var closed = true
        currentNodeStrategy.forEach { pair ->
            val node = pair.first;
            listMaps.add(mutableListOf())
            for(l in node.collectLeaves()){
                when(l){
                    is LogicNode -> {
                        val framing = listModRep[currentNodeStrategy.indexOf(pair)].second.classFrames["main"]!!
                        val exec = AbstractEvaluation(framing)
                        val res = exec.evaluateAndPrecond(l)
                        closed = res.first && closed
                        val precond = res.second
                        listMaps.last().add(Pair(exec.substMap, precond))
                        exec.printSubstMap()
                        //exec.printRawSubstMap()
                    }
                    is StaticNode -> {
                        output("Crowbar: open static leaf ${l.str}", Verbosity.SILENT)
                    }
                }
            }
        }

        output("Crowbar: abstract evaluation result, postconditions of the nodes are verified : $closed")

        return listMaps
    }

    private fun compareMaps(data: List<List<Pair<Map<Location, Term>, LogicElement>>>){
        val listLength = data.map { list -> list.size }
        if (listLength.filter{ it == data[0].size }.size != data.size){
            throw Exception("The number of leaves in version of the program is not the same, that's a bit unexpected, to be dealt with later.")
        }

        for(map in data[0]){
            val listAux = data.map { list -> list[data[0].indexOf(map)] }
            compareMap(listAux)
        }

    }

    private fun compareMap(dataPair : List<Pair<Map<Location, Term>, LogicElement>>){
        val dataMaps = dataPair.map { pair -> pair.first }
        val dataPreconds = dataPair.map { pair -> pair.second }
        val listKeys = dataMaps.map { map -> map.keys }
        val sharedKeys = listKeys.fold(listKeys[0]) { acc, set -> acc.intersect(set) }
        val sameKeys = listKeys.fold(true) {acc, set -> acc && set == sharedKeys }

        if(!sameKeys){
            output("Crowbar: warning not the same set of locations, performing the comparison on the following locations only: $sharedKeys")
        }

        val aux = generateSMT( dataMaps.map { it.filterKeys { key -> key in sharedKeys } }, dataPreconds)
        output("$aux")

        evaluateSMT(aux)
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
        val concAbs = allTerms.filterIsInstance<ConcreteOnAbstractTerm>()
        val unknowns = allTerms.filterIsInstance<UnknownTerm>()
        val absExp = allTerms.filterIsInstance<AbstractFormula>()

        val presSMT = dataPres.joinToString ("\n"){ "(assert ${it.toSMT()}  )" }

        val andEqualities = dataMaps[0].keys.joinToString ("\n\t"){ key -> "(and ( = " + dataMaps.joinToString ( " " ){ it[key]!!.toSMT() } + ")" }
        val closeEqualities = dataMaps[0].keys.joinToString ( "\n\t" ){")"}
        val equalities = "(assert (not $andEqualities $closeEqualities ) )"

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

        val concAbsDecl = concAbs.map {
            "(declare-fun UC_${it.target.name} (${typeOfConcreteTermToSMT(it.value)} Int) Int)"
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
    $concAbsDecl
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