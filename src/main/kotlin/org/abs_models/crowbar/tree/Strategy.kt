package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.types.*
import kotlin.reflect.KClass

interface Strategy{
    fun execute(symbolicNode: SymbolicNode)
}

/*
The default strategy just tries all rules in the given order
 */
class DefaultStrategy(private val rules: List<Rule>) : Strategy{
    override fun execute(symbolicNode: SymbolicNode){
        if(symbolicNode.children.isNotEmpty()) { //if we are not in a leaf, symbolically execute every branch
            symbolicNode.children.filterIsInstance<SymbolicNode>().forEach { execute(it) }
        } else {
            //this is a depth first strategy: apply the matching rule and then recurse on the result
            for (rule in rules) {
                if (rule.isApplicable(symbolicNode.content)) {
                    val next = rule.apply(symbolicNode.content)
                    if (next != null) {
                        symbolicNode.children = next
                        for (node in next) {
                            if (node is SymbolicNode)
                                this.execute(node)
                        }
                    }
                    break
                }
            }
        }
    }
}

/* associates types with strategies */
fun getStrategy(clazz: KClass<out DeductType>, repos: Repository) : Strategy =
    when(clazz){
        PostInvType::class   -> nextPITStrategy(repos)
        LocalTypeType::class -> nextLTTStrategy(repos)
        else                 -> throw Exception("unsupported type $clazz")
    }

//standard verification
fun nextPITStrategy(repos: Repository) : Strategy =
    DefaultStrategy(listOf(PITBranch, PITSyncAssign(repos), PITLocAssign(repos), PITAllocAssign(repos),
                           PITCallAssign(repos), PITSyncCallAssign(repos), PITReturn, PITSkip, PITIf, PITAssert,
                           PITAwait, PITSkipSkip, PITWhile, PITScopeSkip, PITTryPush, PITTryPop, PITThrow))

//local session types
fun nextLTTStrategy(repos: Repository) : Strategy =
    DefaultStrategy(listOf(LTTBranch, LTTSyncAssign(repos), LTTLocAssign(repos), LTTAllocAssign(repos),
                           LTTCallAssign(repos), LTTReturn, LTTSkip, LTTIf, LTTAwait, LTTSkipSkip, LTTWhile,
                           LTTScopeSkip))