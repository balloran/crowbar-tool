
import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.LocalTypeParser
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.LocalTypeType
import org.abs_models.frontend.ast.ClassDecl
import java.nio.file.Paths

class LocalTypeTest : StringSpec() {

    init {
        "matching-1" {
            val exp1 = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true)).role!e(true)", null)
            assert(exp1.matches(LTPatternCall("a")))
            assert(exp1.matches(LTPatternCall("c")))
            assert(exp1.matches(LTPatternCall("d")))
            assert(exp1.matches(LTPatternRep))
            assert(!exp1.matches(LTPatternCall("b")))
            assert(!exp1.matches(LTPatternCall("e")))
        }

        "matching-2" {
            val exp2 = LocalTypeParser.parse("(skip + Get(a)).Susp(true).(Put(true))*", null)
            assert(exp2.matches(LTPatternGet))
            assert(exp2.matches(LTPatternSusp))
            assert(!exp2.matches(LTPatternPut))
            assert(!exp2.matches(LTPatternRep))
        }

        val fakeCallCtx = LTCallContext(True, EmptyUpdate, Const("sth"), mapOf())

        "transform" {
            var exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("a"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("b"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("d"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("e"), fakeCallCtx)
            assert(exp.isSkip)

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("c"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("c"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("c"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("d"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("e"), fakeCallCtx)
            assert(exp.isSkip)

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("d"), fakeCallCtx)
            exp = exp.readTransform(LTPatternCall("e"), fakeCallCtx)
            assert(exp.isSkip)
        }

        "transform-fail" {
            var exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("a"), fakeCallCtx)
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("c"), fakeCallCtx) }

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("c"), fakeCallCtx)
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("a"), fakeCallCtx) }
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("e"), fakeCallCtx) }
        }

        val cvc: String = System.getenv("CVC") ?: "cvc"
        val z3: String = System.getenv("Z3") ?: "z3"

        for (smt in listOf(z3, cvc)) {
            
            "$smt basic local types"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/localtype.abs")))
                val classDecl = model.extractClassDecl("LocalTypeTest", "C")

                testMethod(classDecl, "returnVarSpec", repos, true)
                testMethod(classDecl, "returnVarSpecFail", repos, false)
                testMethod(classDecl, "returnOldSpec", repos, true)
                testMethod(classDecl, "returnOldSpecFail", repos, false)
                testMethod(classDecl, "basicOption", repos, true)
                testMethod(classDecl, "getExpFail", repos, false)
                testMethod(classDecl, "callPrecond", repos, true)
                testMethod(classDecl, "callPrecondFail", repos, false)
                testMethod(classDecl, "suspPrecond", repos, true)
                testMethod(classDecl, "suspPrecondFail", repos, false)
                testMethod(classDecl, "shorthand", repos, true)
            }

            "$smt local types with complex data types"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/localtype.abs")))
                val classDecl = model.extractClassDecl("LocalTypeTest", "C")

                testMethod(classDecl, "returnDataTypeSpec", repos, true)
                testMethod(classDecl, "returnDataTypeSpecFail", repos, false)
                testMethod(classDecl, "returnDataTypeParamSpec", repos, true)
                testMethod(classDecl, "returnDataTypeParamSpecFail", repos, false)
            }

            "$smt local type loops"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/localtype.abs")))
                val classDecl = model.extractClassDecl("LocalTypeTest", "C")

                testMethod(classDecl, "unspecifiedLoop", repos, true)
                testMethod(classDecl, "loopHeadDuplication", repos, true)
                testMethod(classDecl, "loopTailDuplication", repos, true)
                testMethod(classDecl, "nestedRepetition", repos, true)
                testMethod(classDecl, "sideconditionInLoop", repos, true)
                testMethod(classDecl, "sideconditionInLoopFail", repos, false)
                testMethod(classDecl, "singleRepMultiLoop", repos, true)
                testMethod(classDecl, "greedyLoopTrap", repos, true)
            }

            "$smt local type aliasing and sideconditions"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/localtype.abs")))
                val classDecl = model.extractClassDecl("LocalTypeTest", "C")

                testMethod(classDecl, "getExpAliasing", repos, true)
                testMethod(classDecl, "getExpLocalAliasing", repos, true)
                testMethod(classDecl, "getExpLocalAliasingFail", repos, false)
                testMethod(classDecl, "roleFieldAliasing", repos, true)
                testMethod(classDecl, "roleFieldAnonFail", repos, false)
                testMethod(classDecl, "greedyOptionTrap", repos, true)
                testMethod(classDecl, "greedySeqTrap", repos, true)
                testMethod(classDecl, "multipathSidecondtion", repos, true)
                testMethod(classDecl, "multipathSidecondtionFail", repos, false)
                testMethod(classDecl, "multipathLoopAmbiguity", repos, true)
                testMethod(classDecl, "multipathLoopAmbiguityFail", repos, false) // Ideally we'd like this to succeed
            }
        }
    }
}

fun testMethod(classDecl: ClassDecl, method: String, repos: Repository, expected: Boolean) {
    val ltt = LocalTypeType::class
    val node = classDecl.extractMethodNode(ltt, method, repos)
    val res = executeNode(node, repos, ltt)
    println("Method $method result was $res")
    res shouldBe expected
}