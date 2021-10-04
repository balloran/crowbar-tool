package org.abs_models.crowbar.rule

import org.abs_models.crowbar.data.AbstractVar
import org.abs_models.crowbar.data.Anything
import kotlin.reflect.full.superclasses


class MatchCondition{
    var map = mutableMapOf<AbstractVar, Anything>()
    var failReason = "No failure occurred"
        set(value) {
            field = value
            failure = true
        }
    var failure = false
}

fun containsAbstractVar(concrete: Anything) : Boolean{
    return concrete.collectAll(AbstractVar::class).isNotEmpty()
}


/*
*   For reasons unknown, the clone part throws a java.lang.VerifyError
*   This may be a versioning error in the classPath
*   However, this function is currently not used anyway
*
fun apply(pattern : Anything, matchCond : MatchCondition) : Any{

    if(pattern is AbstractVar){
        if(matchCond.map.containsKey(pattern))
           return matchCond.map.getValue(pattern)
        return pattern
    }

    val next = pattern.clone()

    for(field in pattern::class.java.declaredFields) {
        field.isAccessible = true
        val f = field.get(pattern)

        if(!Anything::class.java.isAssignableFrom(field.type)) {
            field.set(next, f)
        }else{
            field.set(next, apply(f as Anything, matchCond))
        }
    }
    return next
}*/


fun match(concrete : Anything, pattern : Anything, matchCond : MatchCondition) {

    fun inMatch(concrete : Anything, pattern : Anything, matchCond : MatchCondition) {
        if (pattern is AbstractVar) {
            //The following checks that we have the right kind of AbstractVar by checking the implemented super class
            //todo: this is buggy because the superclasses[0] access returns Java.lang.Object
            println(pattern::class.superclasses)
            if (pattern::class.superclasses[0].isInstance(concrete)) {
                //This catches abstract variables bound multiple times
                if (matchCond.map.containsKey(pattern) && matchCond.map[pattern] != concrete) {
                    matchCond.failReason = "AbstractVar ${pattern.prettyPrint()} failed unification with two terms: ${matchCond.map[pattern]!!.prettyPrint()} and ${concrete.prettyPrint()}"
                    return
                }
                matchCond.map[pattern] = concrete
                return
            } else {
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

            if (List::class.java.isAssignableFrom(field.type)) {
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
                val f1 = field.get(concrete)
                val f2 = field.get(pattern)
                if(f2 is AbstractVar && f1 is Anything){
                    matchCond.map[f2] = f1
                } else
                if (f1 != f2) {
                    matchCond.failReason = "Value mismatch: ${concrete.prettyPrint()} and ${pattern.prettyPrint()}"
                    return
                }
            } else {
                val next1 = field.get(concrete) as Anything
                val next2 = field.get(pattern) as Anything
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