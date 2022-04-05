package org.abs_models.crowbar.rule

import org.abs_models.crowbar.data.AbstractVar
import org.abs_models.crowbar.data.Anything
import org.abs_models.crowbar.main.output
import kotlin.reflect.full.superclasses

/*
This file contains the unification/matching algorithm.
We use the `AbstractVar` interface to mark variables, which are then unified with a concrete structure.
The algorithm works on arbitrary structures using reflection, which is a bit slow, but easy to extend:
If a class C is added to the Anything hierarchy, one adds an interface I with C <: i and a class AbstractC <: AbstractVar, I.
 */

/* Keeps track of the unifier and failure reason */
class MatchCondition{
    var map = mutableMapOf<AbstractVar, Anything>()
    var failReason = "No failure occurred"
        set(value) {
            field = value
            failure = true
        }
    var failure = false
}

fun containsAbstractVar(concrete: Anything) : Boolean = concrete.collectAll(AbstractVar::class).isNotEmpty()

fun match(concrete : Anything, pattern : Anything, matchCond : MatchCondition) {

    fun inMatch(concrete : Anything, pattern : Anything, matchCond : MatchCondition) {
        if (pattern is AbstractVar) {
            //The following checks that we have the right kind of AbstractVar by checking the implemented super class
            if (pattern::class.superclasses[0].isInstance(concrete)) {
                //This catches abstract variables bound multiple times
                if (matchCond.map.containsKey(pattern) && matchCond.map[pattern] != concrete) {
                    matchCond.failReason = "AbstractVar ${pattern.prettyPrint()} failed unification with two terms: ${matchCond.map[pattern]!!.prettyPrint()} and ${concrete.prettyPrint()}"
                    return
                }
                matchCond.map[pattern] = concrete
                //output("match $concrete with $pattern.")
                return
            } else {
                //output("pattern $pattern \nconcrete $concrete \nconcreteclass ${concrete::class}")
                //output("${pattern::class.superclasses}")
                matchCond.failReason = "AbstractVar ${pattern.prettyPrint()} failed unification because of a type error: ${concrete.prettyPrint()}"
                return
            }
        }

        //Mismatch in the outermost constructor
        if (concrete::class != pattern::class) {
            matchCond.failReason = "Constructor mismatch: ${concrete.prettyPrint()} and ${pattern.prettyPrint()}"
            return
        }

        //Iterate over fields
        for (field in concrete::class.java.declaredFields) {
            field.isAccessible = true

            //output("field: ${field}")

            if (List::class.java.isAssignableFrom(field.type)) {
                //output("chat1 field: ${field}")
                @Suppress("UNCHECKED_CAST")
                val f1: List<Anything> = field.get(concrete) as List<Anything>
                @Suppress("UNCHECKED_CAST")
                val f2: List<Anything> = field.get(pattern) as List<Anything>
                for (i in f1.indices) {
                    inMatch(f1[i], f2[i], matchCond)
                    if (matchCond.failure) return
                }
            }
            //Because we do not match classes from outside our Anything hierarchy, we must compare them using equality
            //This is for, e.g., Strings used for variable names and constants
            else if (!Anything::class.java.isAssignableFrom(field.type)) {
                //output("chat2 field: ${field}")
                val f1 = field.get(concrete)
                val f2 = field.get(pattern)
                //output("f1 ${f1::class} $f1 \nf2 ${f2::class} $f2")
                if(f2 is AbstractVar && f1 is Anything){
                    matchCond.map[f2] = f1
                } else if (f1 != f2) {
                    matchCond.failReason = "Value mismatch: ${concrete.prettyPrint()} and ${pattern.prettyPrint()}"
                    return
                }
            } else {
                //output("chat field: ${field}")
                val next1 = field.get(concrete) as Anything
                val next2 = field.get(pattern) as Anything
                //output("\n$next1 \n$next2 \n")
                if (next1 != concrete && next2 != concrete) {
                    inMatch(next1, next2, matchCond)
                    if (matchCond.failure) return
                }
            }
        }
    }



    if(containsAbstractVar(concrete)){
        matchCond.failReason = "Concrete statement contains abstract variables: ${concrete.prettyPrint()}"
        return
    }
    inMatch(concrete, pattern, matchCond)
}