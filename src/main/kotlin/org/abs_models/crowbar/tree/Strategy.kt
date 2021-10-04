package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.rule.Rule
import org.abs_models.crowbar.types.*
import kotlin.reflect.KClass

interface Strategy{
    fun execute(symbolicNode: SymbolicNode)
}


class DefaultStrategy(private val rules: List<Rule>) : Strategy{

    override fun execute(symbolicNode: SymbolicNode){
        if(symbolicNode.children.isNotEmpty()) {
            symbolicNode.children.filterIsInstance<SymbolicNode>().forEach { execute(it) }
        } else {
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

fun getStrategy(clazz: KClass<out DeductType>, repos: Repository) : Strategy{
    return when(clazz){
        PostInvType::class   -> nextPITStrategy(repos)
        RegAccType::class    -> nextRAStrategy()
        LocalTypeType::class -> nextLTTStrategy(repos)
        else                 -> throw Exception("unsupported type $clazz")
    }
}


fun nextRAStrategy(): Strategy = DefaultStrategy(listOf(RAReturn, RAFieldAssign, RAVarAssign, RASkip, RASkipSkip))
fun nextPITStrategy(repos: Repository) : Strategy = DefaultStrategy(listOf(PITBranch, PITSyncAssign(repos), PITLocAssign(repos), PITAllocAssign(repos), PITCallAssign(repos), PITSyncCallAssign(repos), PITReturn, PITSkip, PITIf, PITAssert, PITAwait, PITSkipSkip, PITWhile, PITScopeSkip))
fun nextLTTStrategy(repos: Repository) : Strategy = DefaultStrategy(listOf(LTTBranch, LTTSyncAssign(repos), LTTLocAssign(repos), LTTAllocAssign(repos), LTTCallAssign(repos), LTTReturn, LTTSkip, LTTIf, LTTAwait, LTTSkipSkip, LTTWhile, LTTScopeSkip))
