package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.evaluateSMT
import org.abs_models.crowbar.interfaces.getSMT
import org.abs_models.crowbar.interfaces.smtHeader
import org.abs_models.crowbar.interfaces.valueOf
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.tree.*
import org.abs_models.frontend.ast.Model
import java.lang.reflect.Executable
import java.nio.file.Path

class RelationExecution(private val filePaths: List<Path>){

    var listModRep: List<Pair<Model, Repository>> = emptyList()
    var listNode: List<SymbolicNode> = emptyList()

    var listStrategy: List<Strategy> = emptyList()

    var listNodeStrat: List<Pair<SymbolicNode, Strategy>> = emptyList()

    var listFraming: List<Map<Location, AELocSet>> = emptyList()
    var listMaps: MutableList<MutableMap<Location, Term>> = mutableListOf()

    init {
        loadFiles()
        //extractMainNodes()
        getStrategies()
        extractNodeStrat()
    }

    private fun loadFiles(){
        listModRep = filePaths.map { path -> load(listOf(path)) }
    }

    private fun extractNodeStrat(){
        listNodeStrat = listModRep.map { pair ->
            Pair(
                pair.first.extractMainNode(AbstractType::class),
                getStrategy(AbstractType::class, pair.second, "main")
            )
        }
    }

    private fun extractMainNodes(){
        listNode = listModRep.map { pair -> pair.first.extractMainNode(AbstractType::class) }
        output("$listNode")
    }

    private fun getStrategies(){
        listStrategy = listModRep.map { pair -> getStrategy(AbstractType::class, pair.second, "main") }
    }

    fun simpleExecute(){
        listNodeStrat.forEach { pair -> pair.second.execute(pair.first) }

        listModRep.forEach { pair -> val repos = pair.second;
            for(key in repos.classFrames.keys){
                repos.classFrames[key]?.set(AELocation("nothing"), AELocSet(emptyList()))
            }
            //output("${repos.classFrames}")
        }
        listFraming = listModRep.map { pair -> pair.second.classFrames["main"]!! }

        var closed = true
        listNodeStrat.forEach { pair ->
            val node = pair.first;
            for(l in node.collectLeaves()){
                when(l){
                    is LogicNode -> {
                        val exec = AbstractExecution(listFraming[listNodeStrat.indexOf(pair)])
                        closed = exec.evaluate(l) && closed
                        listMaps.add(exec.substMap)
                        exec.printSubstMap()
                        output("\n")
                        //exec.printRawSubstMap()
                    }
                    is StaticNode -> {
                        output("Crowbar: open static leaf ${l.str}", Verbosity.SILENT)
                    }
                }
            }
        }

        output("Crowbar: relational execution result, postconditions are verified : $closed")
        output("Crowbar: start of final state comparison.")

        val same = compareMaps()

        output("Crowbar: comparison of final states result: $same")
    }

    private fun compareMaps() : Boolean {
        val keys = listMaps[0].keys

        // check later that keys are fine in every map

        //output("$listMaps")

        var res = true
        keys.forEach{key ->
            val values = listMaps.map { valMap -> valMap[key]!! }
            res = compareValues(values) && res
        }

        return res
    }

    private fun compareValues(values : List<Term>) : Boolean{
        val size = values.size
        var res = true

        var i = 1

        while(i < size && res){
            res = compareTwoValues(values[0], values[i]) && res
            i++
        }

        return res
    }

    private fun compareTwoValues(val1 : Term, val2 : Term) : Boolean{
        if(val1::class != val2::class){
            return false
        }
        when (val1){
            is FullAbstractTerm -> {
                val2 as FullAbstractTerm
                if(val1.name != val2.name ||
                    val1.arity != val2.arity ||
                    val1.maxArity != val2.maxArity ||
                    val1.arity >= val1.maxArity ||
                    val1.accessiblesValues.size != val2.accessiblesValues.size){
                    return false
                }
                val list1 = val1.accessiblesValues as MutableList
                val list2 = val2.accessiblesValues as MutableList

                var res = true
                while(list1.isNotEmpty() && res){
                    val aux1 = list1.removeFirst()
                    val aux2 = list2.removeFirst()
                    res = compareTwoValues(aux1, aux2) && res
                }
                return res
            }
            is PartialAbstractTerm -> {
                val2 as PartialAbstractTerm
                if(val1.name != val2.name ||
                    val1.arity != val2.arity ||
                    val1.maxArity != val2.maxArity ||
                    val1.arity >= val1.maxArity ||
                    val1.accessiblesValues.size != val2.accessiblesValues.size ){
                    return false
                }
                val list1 = val1.accessiblesValues as MutableList
                val list2 = val2.accessiblesValues as MutableList
                list1.add(val1.initialValue)
                list2.add(val2.initialValue)

                var res = true
                while(list1.isNotEmpty() && res){
                    val aux1 = list1.removeFirst()
                    val aux2 = list2.removeFirst()
                    res = compareTwoValues(aux1, aux2) && res
                }
                return res
            }
            is ConcreteOnAbstractTerm -> {
                val2 as ConcreteOnAbstractTerm

                val data1 = AEnormalize(Pair(val1, emptyList()))
                val data2 = AEnormalize(Pair(val2, emptyList()))

                //output("$data1")

                if(!compareTwoValues(data1.first, data2.first)){
                    return false
                }

                val map1 = mutableMapOf<ProgVar, Term>()
                val map2 = mutableMapOf<ProgVar, Term>()

                //output("${data1.second} \n\n ${data1.second[0]} \n\n ${data1.second.first()}")

                val list1 = data1.second.reversed().toMutableList()
                val list2 = data2.second.reversed().toMutableList()

                while(list1.isNotEmpty()){
                    val aux1 = list1.removeFirst()
                    map1[aux1.first] = aux1.second
                }


                while(list2.isNotEmpty()){
                    val aux2 = list2.removeFirst()
                    map2[aux2.first] = aux2.second
                }

                if(map1.keys != map2.keys){
                    return false
                }

                var res = true
                for(key in map1.keys){
                    res = compareTwoValues(map1[key]!!, map2[key]!!) && res
                    if(!res) break
                }
                return res

            }
            is UnknownTerm -> {
                return val1 == val2
            }
            is org.abs_models.crowbar.data.Function -> {
                val2 as org.abs_models.crowbar.data.Function

                val aeTerms1 = findAETerm(val1)
                val aeTerms2 = findAETerm(val2)

                val mapTerms = mapAETerm(aeTerms1 , aeTerms2)

                //output("$val1 $val2")

                return checkFunction(val1, val2, mapTerms)
            }
            else -> {
                throw Exception("Unwanted term in map comparison : $val1")
            }
        }
    }

    fun AEnormalize(data : Pair<AbstractTerm, List<Pair<ProgVar, Term>>>): Pair<AbstractTerm, List<Pair<ProgVar, Term>>>{
        return when (data.first){
            is ConcreteOnAbstractTerm -> {
                val aux = data.first as ConcreteOnAbstractTerm;
                AEnormalize(
                    Pair(
                        aux.abstract,
                        data.second + Pair(aux.target, aux.value)
                    )
                )
            }
            else -> {
                data
            }
        }
    }

    fun findAETerm(function : org.abs_models.crowbar.data.Function) : List<Term>{
        return function.params.map {
                param -> if(param is org.abs_models.crowbar.data.Function) {findAETerm(param)} else listOf(param)
        }.flatten()
    }

    fun mapAETerm(terms1 : List<Term>, terms2: List<Term>): Map<Term, Int>{

        val uf = UnionFind(terms1 + terms2)

        for(term1 in terms1){
            for(term2 in terms2){
                if(compareTwoValues(term1, term2)){
                    uf.union(term1, term2)
                }
            }
        }

        return uf.mapRes

    }

    fun checkFunction(val1: Term, val2: Term, mapTerms : Map<Term, Int>) : Boolean{

        //output("${customToSmt(val1, mapTerms)} == ${customToSmt(val2, mapTerms)}")

        var abstractconst = ""

        for(key in mapTerms.keys){
            abstractconst += "\ndeclare-const $mapTerms[key]"
        }

        val smtString =
        """
;equality
    (assert (not (= ${customToSmt(val1, mapTerms)} ${customToSmt(val2, mapTerms)})))
    (check-sat)
    (exit)
    """.trimIndent()

        output(smtString)
        val res = evaluateSMT(smtString)


        //output("$smtString\n$res \n\n")
        return res
    }

    fun customToSmt(term: Term, mapTerm : Map<Term, Int>): String{
        return when (term){
            is UnknownTerm -> term.toSMT()
            is AbstractTerm -> "aeterm" + mapTerm[term].toString()
            is org.abs_models.crowbar.data.Function -> {

                if(term.params.isEmpty()) {
                    if(term.name.startsWith("-")) return "(- ${term.name.substring(1)})" //CVC4 requires -1 to be passed as (- 1)
                    return term.name
                }

                val list = term.params.fold("") { acc, nx -> acc + " ${customToSmt(nx, mapTerm)}" }
                getSMT(term.name, list)
            }
            else -> throw Exception("Unwanted term in customSmt : $term")
        }
    }
}

class UnionFind(terms : List<Term>){

    val mapRes : MutableMap<Term, Int>
    val auxRes : MutableMap<Int, Term> = mutableMapOf()
    init{
        mapRes = terms.associateWith { term -> term.hashCode() } as MutableMap
        for(key in mapRes.keys){
            auxRes[mapRes[key]!!] = key
        }
    }

    fun union(term1 : Term, term2 : Term){
        val racine1 = find(term1)
        val racine2 = find(term2)
        if(racine1 != racine2){
            mapRes[auxRes[racine1]!!] = racine2
        }
    }

    fun find(term : Term) : Int{
        if(mapRes[term] != term.hashCode()){
            mapRes[term] = find(auxRes[mapRes[term]!!]!!)
        }
        return mapRes[term]!!
    }
}