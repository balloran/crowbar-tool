package org.abs_models.crowbar.tree

import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.main.output
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
        //output("${symbolicNode}\n")
        if(symbolicNode.children.isNotEmpty()) { //if we are not in a leaf, symbolically execute every branch
            symbolicNode.children.filterIsInstance<SymbolicNode>().forEach { execute(it) }
        } else {
            //this is a depth first strategy: apply the matching rule and then recurse on the result
            for (rule in rules) {
                //output("$rule")
                if (rule.isApplicable(symbolicNode.content)) {
                    output("$rule")
                    val next = rule.apply(symbolicNode.content)
                    if (next != null) {
                        if(symbolicNode.info is LeafInfo) {
                            println("Prop: "+ symbolicNode.info)
                            next.forEach {
                                if (it.info is NoInfo) {
                                    it.info = symbolicNode.info
                                }
                            }
                        }
                        symbolicNode.children = next
                        for (node in next) {
                            //output("$node\n")
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

/* This associates types with strategies */
fun getStrategy(clazz: KClass<out DeductType>, repos: Repository, classdecl : String = "") : Strategy =
    when(clazz){
        PostInvType::class   -> nextPITStrategy(repos)
        LocalTypeType::class -> nextLTTStrategy(repos)
        AbstractType::class -> nextAEStrategy(repos, classdecl)
        else                 -> throw Exception("unsupported type $clazz")
    }

//standard verification
fun nextPITStrategy(repos: Repository) : Strategy =
    DefaultStrategy(listOf(PITBranch(repos), PITSyncAssign(repos), PITLocAssign(repos), PITAllocAssign(repos),
                           PITCallAssign(repos), PITSyncCallAssign(repos), PITReturn(repos), PITSkip, PITIf(repos),
                           PITAssert(repos), PITAwait(repos), PITSkipSkip, PITWhile, PITScopeSkip, PITTryPush,
                           PITTryPop, PITThrow, PITExpr(repos)))

//local session types
fun nextLTTStrategy(repos: Repository) : Strategy =
    DefaultStrategy(listOf(LTTBranch, LTTSyncAssign(repos), LTTLocAssign(repos), LTTAllocAssign(repos),
                           LTTCallAssign(repos), LTTReturn, LTTSkip, LTTIf, LTTAwait, LTTSkipSkip, LTTWhile,
                           LTTScopeSkip))

//abstract execution
fun nextAEStrategy(repos:Repository, classdecl: String): Strategy =
    DefaultStrategy(listOf(AESimpleAbstractAssign(repos), AESkipSkip, AESkip, AELocAssign(repos, classdecl), AEIf(repos), AEScopeSkip))