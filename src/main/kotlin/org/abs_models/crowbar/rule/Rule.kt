package org.abs_models.crowbar.rule

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.main.ADTRepos
import org.abs_models.crowbar.tree.SymbolicTree
import org.abs_models.crowbar.types.AccVar
import org.abs_models.frontend.typechecker.Type

//do not use variables starting with pv_ etc.
//todo: make some less intrusive restrictions
object FreshGenerator {
    private var count = 0
    fun getFreshProgVar(dType : Type, isFuture:Boolean=false) : ProgVar {
        return ProgVar("pv_" + (count++), dType.qualifiedName, dType)
    }
    fun getFreshPP() : PP {
        return PPId(count++)
    }
    fun getFreshFuture(dType : Type) : ProgVar {
        return ProgVar("fut_"+ (count++), dType.qualifiedName, ADTRepos.model!!.getFutType(dType))
    }
    fun getFreshFunction() : Function {
        return Function("f_"+ (count++), emptyList())
    }
	fun getFreshObjectId(className: String, map: List<Expr>): Expr {
        if(map.isEmpty())
            return SExpr("NEW"+(count++)+"_"+map.size, listOf(SExpr(className, emptyList())))
        return SExpr("NEW"+(count++)+"_"+map.size, listOf(SExpr(className, emptyList()))+map)
	}
    fun getFreshRAVar() : AccVar{
        return AccVar("RA_A"+(count++))
    }
    fun reset(){ count = 0 } //test only
}

abstract class Rule(
        private val conclusion : Modality
){
    private var lastState : SymbolicState? = null
    private var cache : MatchCondition? = null

    fun isApplicable(input : SymbolicState) : Boolean {
        return !this.generateMatchCondition(input).failure
    }

    private fun generateMatchCondition(input : SymbolicState) : MatchCondition{
        if(lastState == input) return cache as MatchCondition
        val cond = MatchCondition()
        match(input.modality.remainder, conclusion.remainder, cond)
        match(input.modality.target, conclusion.target, cond)
        lastState = input
        cache = cond
        return cond
    }
    fun apply(input : SymbolicState) : List<SymbolicTree>?{
        val cond = generateMatchCondition(input)
        if(cond.failure) return null

        val ret= transform(cond, input).map { it.normalize(); it }
        if(ret.any{ it.hasAbstractVar() }) return null
        return ret
    }

    abstract fun transform(cond : MatchCondition, input: SymbolicState) : List<SymbolicTree>
}

