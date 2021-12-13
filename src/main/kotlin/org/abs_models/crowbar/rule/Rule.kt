package org.abs_models.crowbar.rule

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnionType

//do not use variables starting with pv_ etc.
object FreshGenerator {
    private var count = 0
    fun getFreshProgVar(dType : Type) : ProgVar = ProgVar("pv_" + (count++), dType)
    fun getFreshPP() : PP = PPId(count++)
    fun getFreshFuture(dType : Type) : ProgVar = ProgVar("fut_"+ (count++), ADTRepos.model!!.getFutType(dType))

    fun getFreshObjectId(className: String, map: List<Expr>, type: Type): Expr {
        val newName = "NEW"+(count++)+"_"+map.size
        if (type is UnionType)
            ADTRepos.objects[newName] = type
        if(map.isEmpty())
            return SExpr(newName, listOf(SExpr(className, emptyList())))
        return SExpr(newName, listOf(SExpr(className, emptyList()))+map)
    }
}

/* Every rule has a conclusion scheme that it matches on */
abstract class Rule(
        private val conclusion : Modality
){
    //some simple caching
    private var lastState : SymbolicState? = null
    private var cache : MatchCondition? = null

    fun isApplicable(input : SymbolicState) : Boolean {
        return !this.generateMatchCondition(input).failure
    }

    /* Tries to match on a concrete symbolic syste */
    private fun generateMatchCondition(input : SymbolicState) : MatchCondition{
        //caching
        if(lastState == input) return cache as MatchCondition

        //matching
        val cond = MatchCondition()
        match(input.modality.remainder, conclusion.remainder, cond)
        match(input.modality.target, conclusion.target, cond)

        //caching
        lastState = input
        cache = cond
        return cond
    }

    /* tries to apply the rule, returns either the branches generated by the rule or null if it fails */
    fun apply(input : SymbolicState) : List<SymbolicTree>?{
        val cond = generateMatchCondition(input)
        if(cond.failure) return null

        val ret= transform(cond, input).map { it.normalize(); it }
        if(ret.any{ it.hasAbstractVar() }) return null
        return ret
    }

    /* This is where the rule itself is executed */
    abstract fun transform(cond : MatchCondition, input: SymbolicState) : List<SymbolicTree>
}

