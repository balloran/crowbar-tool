package org.abs_models.crowbar.types

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
import java.text.Normalizer.Form
import kotlin.reflect.jvm.internal.impl.descriptors.Visibilities.Unknown

class AbstractExecution (val framing: Map<Location, AELocSet>){
    val substMap: MutableMap<Location, Term> = mutableMapOf()

    init{
        for(location in this.framing.keys){
            this.substMap[location] = UnknownTerm(location)
        }
    }

    fun evaluate(l : SymbolicLeaf) : Boolean {
        if (l is StaticNode){
            return false
        }
        l as LogicNode
        if(l.isEvaluated){
            return l.isValid
        }

        val pre = this.eval(this.deupdatify(l.ante))
        val post = this.eval(this.deupdatify(Not(l.succ)))

        output("${pre.prettyPrint()}\n\n${post.prettyPrint()}")

        val smtRep = generateSMT(pre, post)

        return evaluateSMT(smtRep)
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
        when(update){
            is ChainUpdate -> {this.apply(update.left); this.apply(update.right)}
            is ElementaryUpdate -> concreteApply(update.lhs, update.rhs)
            is AbstractUpdate -> abstractApply(update.name, update.accessible, update.assignable)
        }
    }

    private fun concreteApply(elem : ProgVar, term : Term){
        val value = this.eval(term)

        // Expand the concrete update to the abstract location concerned
        for(pair in this.framing[elem]!!.locs){
            val loc = pair.second
            assert(loc is AELocation)
            this.substMap[loc] = ConcreteOnAbstractTerm(elem, value as Term, this.substMap[loc] as AbstractTerm)
        }

        this.substMap.remove(elem)
        this.substMap[elem] = value as Term
    }

    // Apply the abstract update to the current substMap
    private fun abstractApply(name: ConcreteName, accessible : AELocSet, assignable :AELocSet){
        val maxArity = assignable.locs.size
        val listAccessibleValue = accessible.locs.map { pair ->  this.substMap[pair.second]!!}

        // This list will have to be split according to hasTo most likely...
        val listDirectAssignable = assignable.locs.map { pair -> pair.second }
        val listIndirectAssignable = listDirectAssignable.map { loc -> this.framing[loc] }.map { locSet -> locSet?.locs!!.map { pair -> pair.second } }.flatten()

        // Update the value of the specified assignables
        for(loc in listDirectAssignable){
            var type : Type = UnknownType.INSTANCE
            if(loc is ProgVar){
                type = loc.concrType
            }

            val updateValue = FullAbstractTerm(name, listDirectAssignable.indexOf(loc), maxArity, listAccessibleValue, type)
            this.substMap[loc] = updateValue
        }

        // Update the values of locs that are not disjoint with the specified assignables
        var extraArity = maxArity
        for(loc in listIndirectAssignable){
            var type : Type = UnknownType.INSTANCE
            if(loc is ProgVar){
                type = loc.concrType
            }

            val updateValue = FullAbstractTerm(name, extraArity, maxArity, listAccessibleValue, type)
            extraArity += 1
            this.substMap[loc] = updateValue
        }
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