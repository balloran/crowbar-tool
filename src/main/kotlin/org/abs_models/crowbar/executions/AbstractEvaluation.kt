package org.abs_models.crowbar.executions

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.interfaces.evaluateSMT
import org.abs_models.crowbar.interfaces.generateSMT
import org.abs_models.crowbar.main.output
import org.abs_models.crowbar.tree.LogicNode
import org.abs_models.crowbar.tree.StaticNode
import org.abs_models.crowbar.tree.SymbolicLeaf
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnknownType

class AbstractEvaluation (val framing: Map<Location, AELocSet>,
                          val substMap: MutableMap<Location, Term> = mutableMapOf()
){

    init{
        initSubstMap()
        //printFraming()
    }

    private fun initSubstMap(){
        for(location in this.framing.keys){
            this.substMap[location] = UnknownTerm(location)
        }
    }

    private fun printFraming(){
        output(this.framing.toList().joinToString("\n") { pair -> "${pair.first.prettyPrint()}\t\t${pair.second.prettyPrint()}" })
    }

    fun printSubstMap(){
        output(this.substMap.toList().joinToString("\n") { pair -> "${pair.first.prettyPrint()}\t\t${pair.second.prettyPrint()}" } + "\n")
    }

    fun printRawSubstMap() {
        output(this.substMap.toList().joinToString("\n") { pair -> "${pair.first.prettyPrint()}\t\t${pair.second}" })
    }

    fun evaluate(l : SymbolicLeaf) : Boolean {
        //output("$l")
        if (l is StaticNode){
            return false
        }
        l as LogicNode
        if(l.isEvaluated){
            return l.isValid
        }

        val pre = this.eval(this.deupdatify(l.ante))
        //output("${l.ante.prettyPrint()}")
        //output("$pre")
        initSubstMap()
        val post = this.eval(this.deupdatify(Not(l.succ)))

        //output("${l.succ}")
        //output("${post.toSMT()}")

        val smtRep = generateSMT(pre, post)

        //output(smtRep)

        return evaluateSMT(smtRep)
    }

    fun evaluateAndPrecond(l : SymbolicLeaf) : Pair<Boolean, LogicElement>{
        //output("$l")
        if (l is StaticNode){
            return Pair(false, True)
        }
        l as LogicNode
        if(l.isEvaluated){
            return Pair(l.isValid, True)
        }

        val pre = this.eval(this.deupdatify(l.ante))
        //output("${l.ante.prettyPrint()}")
        //output("$pre")
        initSubstMap()
        val post = this.eval(this.deupdatify(Not(l.succ)))

        //output("${l.succ}")
        //output("${post.toSMT()}")

        val smtRep = generateSMT(pre, post)

        //output(smtRep)

        return Pair(evaluateSMT(smtRep), pre)
    }

    fun deupdatify(input : LogicElement) : LogicElement{
        return when(input){
            is UpdateOnFormula -> {apply(input.update); deupdatify(input.target)}
            is UpdateOnTerm -> {apply(input.update); deupdatify(input.target)}
            is Function -> Function(input.name, input.params.map { p -> this.deupdatify(p) as Term })
            is Predicate -> Predicate(input.name, input.params.map { p -> this.deupdatify(p) as Term })
            is Impl -> Impl(this.deupdatify(input.left) as Formula, this.deupdatify(input.right) as Formula)
            is And -> And(this.deupdatify(input.left) as Formula, this.deupdatify(input.right) as Formula)
            is Or -> Or(this.deupdatify(input.left) as Formula, this.deupdatify(input.right) as Formula)
            is Not -> Not(this.deupdatify(input.left) as Formula)
            else -> input
        }
    }

    // Apply the update to the substMap
    fun apply(update : UpdateElement){
        //printSubstMap()
        //output("$update")
        when(update){
            is ChainUpdate -> {this.apply(update.left); this.apply(update.right)}
            is ElementaryUpdate -> concreteApply(update.lhs, update.rhs)
            is AbstractUpdate -> abstractApply(update.name, update.accessible, update.assignable)
        }
    }

    private fun concreteApply(elem : ConcreteLocation, term : Term){
        val value = this.eval(term)

        // Expand the concrete update to the abstract location concerned
        for(pair in this.framing[elem]!!.locs){
            val loc = pair.second
            assert(loc is AELocation)

            when(val aux = this.substMap[loc]!!){
                is PreciseOnAbstractTerm -> {
                    aux.updates[elem] = value as Term
                    this.substMap[loc] = aux
                }
                is AbstractTerm -> {
                    this.substMap[loc] = PreciseOnAbstractTerm(mutableMapOf(Pair(elem, value as Term)), aux)
                }
                else -> {
                    throw Exception("Unforeseen value for abstract location $loc: $aux")
                }
            }

            //this.substMap[loc] = ConcreteOnAbstractTerm(elem, value as Term, this.substMap[loc] as AbstractTerm)
        }

        this.substMap.remove(elem)
        this.substMap[elem] = value as Term
    }

    // Apply the abstract update to the current substMap
    private fun abstractApply(name: ConcreteName, accessible : AELocSet, assignable :AELocSet){
        //printSubstMap()
        //output("${name.name}")
        val maxArity = assignable.locs.size
        val listAccessibleValue = accessible.locs.map { pair ->  this.substMap[pair.second]!!}

        // This list is used for the arity
        val listDirectAssignable = assignable.locs.map { pair -> pair.second }
        //val listIndirectAssignable = listDirectAssignable.map { loc -> this.framing[loc] }.map { locSet -> locSet?.locs!!.map { pair -> pair.second } }.flatten()

        //output("$listDirectAssignable")

        // Split according to hasTo
        val listHasToDirectAssignable = assignable.locs.filter { it.first }.map { pair -> pair.second}
        val listOtherDirectAssignable = assignable.locs.filter{!it.first}.map { pair -> pair.second }



        // Find the concrete locations that are included in the hasTo abstract locations
        val listConcreteHasToIndirectAssignable = listHasToDirectAssignable.map { loc ->
            this.framing[loc]
        }.map { locSet ->
            locSet?.locs!!.map { it.second }.filterIsInstance<ConcreteLocation>()
        }.flatten()

        //output("$assignable")
        //output("${listOtherDirectAssignable}")

        val listOtherIndirectAssignable = listHasToDirectAssignable.map { loc ->
            this.framing[loc]
        }.flatMap { locSet ->
            locSet?.locs!!.filter {
                it.second !is ConcreteLocation
            }.map { pair ->
                pair.second
            }
        } +
                listOtherDirectAssignable.map { loc ->
                    this.framing[loc]
                }.flatMap { locSet ->
                    locSet?.locs!!.map { pair ->
                        pair.second
                    }
                }


        // Todo: Isolate abstract locations that are eligible to become preciseOnAbstractTerm and reconstruct the Term


        var extraArity = maxArity

        // Update the values of the hasTo locations
        for(loc in listHasToDirectAssignable + listConcreteHasToIndirectAssignable){
            var type : Type = UnknownType.INSTANCE
            if(loc is ProgVar){
                type = loc.concrType
            }

            var arity : Int
            if(listDirectAssignable.contains(loc)){
                arity = listDirectAssignable.indexOf(loc)
            }
            else{
                arity = extraArity
                extraArity++
            }

            val updateValue = FullAbstractTerm(name, arity, maxArity, listAccessibleValue, type)
            this.substMap[loc] = updateValue
        }

        //Update the values of the direct hasTo locations
        for(loc in listOtherDirectAssignable){
            var type : Type = UnknownType.INSTANCE
            if(loc is ProgVar){
                type = loc.concrType
            }
            if(loc is Field){
                type = loc.concrType
            }

            val updateValue = PartialAbstractTerm(name, listDirectAssignable.indexOf(loc), maxArity, listAccessibleValue, this.substMap[loc]!!,type)
            this.substMap[loc] = updateValue
        }

        // Update the values of the indirect non hasTo locations
        for(loc in listOtherIndirectAssignable){
            var type : Type = UnknownType.INSTANCE
            if(loc is ProgVar){
                type = loc.concrType
            }
            if(loc is Field){
                type = loc.concrType
            }

            val updateValue = PartialAbstractTerm(name, extraArity, maxArity, listAccessibleValue, this.substMap[loc]!!,type)
            extraArity += 1
            this.substMap[loc] = updateValue
        }

        //printSubstMap()
    }

    // Evaluate the input according to the current substMap
    private fun eval(input:LogicElement) : LogicElement{
        if(input is Location && this.substMap.containsKey(input)){
            return this.substMap.getValue(input)
        }
        when(input){
            is UpdateElement -> throw Exception("Can there really be an update here??")
            is DataTypeConst -> return DataTypeConst(input.name, input.concrType, input.params.map { p -> this.eval(p) as Term })
            is Function -> return Function(input.name, input.params.map { p -> this.eval(p) as Term })
            is Predicate -> return Predicate(input.name, input.params.map { p -> this.eval(p) as Term })
            is Impl -> return Impl(this.eval(input.left) as Formula, this.eval(input.right) as Formula)
            is And -> return And(this.eval(input.left) as Formula, this.eval(input.right) as Formula)
            is Or -> return Or(this.eval(input.left) as Formula, this.eval(input.right) as Formula)
            is Not -> return Not(this.eval(input.left) as Formula)
            is ImplementsTerm -> return ImplementsTerm(this.eval(input.variable) as Term, input.interfaceType)
            is ImplementsForm -> return ImplementsForm(this.eval(input.variable) as Term, input.interfaceType)
            is UpdateOnTerm -> throw Exception("Can there really be updateonTerm here??")
            is UpdateOnFormula -> throw Exception("Can there really be update on form here??")
            else -> return input
        }
    }
}