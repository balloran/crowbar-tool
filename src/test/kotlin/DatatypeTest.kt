import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths
import kotlin.system.exitProcess

class DatatypeTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")

        "$smt simpleDataTypes"{
            smtPath = smt

            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "C")

            val caseSimpleSuccess = classDecl.extractMethodNode(postInv, "caseSimpleSuccess", repos)
            executeNode(caseSimpleSuccess, repos, postInv) shouldBe true

            val caseSimpleFail = classDecl.extractMethodNode(postInv, "caseSimpleFail", repos)
            executeNode(caseSimpleFail, repos, postInv) shouldBe false

            val caseFail = classDecl.extractMethodNode(postInv, "caseFail", repos)
            executeNode(caseFail, repos, postInv) shouldBe false

            val constReturnSuccess = classDecl.extractMethodNode(postInv, "constReturnSuccess", repos)
            executeNode(constReturnSuccess, repos, postInv) shouldBe true

            val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
            executeNode(trivialSuccess, repos, postInv) shouldBe true

            val whileSuccess = classDecl.extractMethodNode(postInv, "whileSuccess", repos)
            executeNode(whileSuccess, repos, postInv) shouldBe true

            val ifExpSuccess = classDecl.extractMethodNode(postInv, "ifExpSuccess", repos)
            executeNode(ifExpSuccess, repos, postInv) shouldBe true

            val ifExpFail = classDecl.extractMethodNode(postInv, "ifExpFail", repos)
            executeNode(ifExpFail, repos, postInv) shouldBe false

        }

        "$smt mixedHeapsTest"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "D")

            val mixedHeapSuccess = classDecl.extractMethodNode(postInv, "mixedHeapSuccess", repos)
            executeNode(mixedHeapSuccess, repos, postInv) shouldBe true

            val awaitSuccess = classDecl.extractMethodNode(postInv, "awaitSuccess", repos)
            executeNode(awaitSuccess, repos, postInv) shouldBe true

            val awaitWhileSuccess = classDecl.extractMethodNode(postInv, "awaitWhileSuccess", repos)
            executeNode(awaitWhileSuccess, repos, postInv) shouldBe true

            val simpleOldSuccess = classDecl.extractMethodNode(postInv, "simpleOldSuccess", repos)
            executeNode(simpleOldSuccess, repos, postInv) shouldBe true

            val simpleOldFail = classDecl.extractMethodNode(postInv, "simpleOldFail", repos)
            executeNode(simpleOldFail, repos, postInv) shouldBe false

            val simpleLastSuccess = classDecl.extractMethodNode(postInv, "simpleLastSuccess", repos)
            executeNode(simpleLastSuccess, repos, postInv) shouldBe true

            val simpleLastFail = classDecl.extractMethodNode(postInv, "simpleLastFail", repos)
            executeNode(simpleLastFail, repos, postInv) shouldBe false

            val syncCallSuccess = classDecl.extractMethodNode(postInv, "syncCallSuccess", repos)
            executeNode(syncCallSuccess, repos, postInv) shouldBe true

        }

        "$smt dTypeAsParamObjectCreation"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "E")

            val moreFieldsThanValuesFail = classDecl.extractMethodNode(postInv, "simpleSuccess", repos)
            executeNode(moreFieldsThanValuesFail, repos, postInv) shouldBe true
        }

        "$smt dTypeFuncTest"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "D")

            val trivialFuncSuccess = classDecl.extractMethodNode(postInv, "trivialFuncSuccess", repos)
            executeNode(trivialFuncSuccess, repos, postInv) shouldBe true

            val caseReturnFunc = classDecl.extractMethodNode(postInv, "caseReturnFunc", repos)
            executeNode(caseReturnFunc, repos, postInv) shouldBe true

            val nonIntParamsSuccess = classDecl.extractMethodNode(postInv, "nonIntParamsSuccess", repos)
            executeNode(nonIntParamsSuccess, repos, postInv) shouldBe true

        }
        "$smt simpleDataTypesParams"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypesparams.abs")))
            val classDecl = model.extractClassDecl("DTypesPar", "C")

            val constReturnSuccess = classDecl.extractMethodNode(postInv, "constReturnSuccess", repos)
            executeNode(constReturnSuccess, repos, postInv) shouldBe true

            val wrapIntConstSuccess = classDecl.extractMethodNode(postInv, "wrapIntConstSuccess", repos)
            executeNode(wrapIntConstSuccess, repos, postInv) shouldBe true

            val wrapBoolConstSuccess = classDecl.extractMethodNode(postInv, "wrapBoolConstSuccess", repos)
            executeNode(wrapBoolConstSuccess, repos, postInv) shouldBe true

            val wrapWrapIntConstSuccess = classDecl.extractMethodNode(postInv, "wrapWrapIntConstSuccess", repos)
            executeNode(wrapWrapIntConstSuccess, repos, postInv) shouldBe true

            val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
            executeNode(trivialSuccess, repos, postInv) shouldBe true

            val trivialNotEqSuccess = classDecl.extractMethodNode(postInv, "trivialNotEqSuccess", repos)
            executeNode(trivialNotEqSuccess, repos, postInv) shouldBe true

            val caseSimpleSuccess = classDecl.extractMethodNode(postInv, "caseSimpleSuccess", repos)
            executeNode(caseSimpleSuccess, repos, postInv) shouldBe true

            val trivialFail = classDecl.extractMethodNode(postInv, "trivialFail", repos)
            executeNode(trivialFail, repos, postInv) shouldBe false

            val caseSimpleFail = classDecl.extractMethodNode(postInv, "caseSimpleFail", repos)
            executeNode(caseSimpleFail, repos, postInv) shouldBe false

            val caseWrappedSuccess = classDecl.extractMethodNode(postInv, "caseWrappedSuccess", repos)
            executeNode(caseWrappedSuccess, repos, postInv) shouldBe true

            val caseWrappedFail = classDecl.extractMethodNode(postInv, "caseWrappedFail", repos)
            executeNode(caseWrappedFail, repos, postInv) shouldBe false

            val multiWrapSimpleSuccess = classDecl.extractMethodNode(postInv, "multiWrapSimpleSuccess", repos)
            executeNode(multiWrapSimpleSuccess, repos, postInv) shouldBe true

            val caseWrappedWrappedSuccess = classDecl.extractMethodNode(postInv, "caseWrappedWrappedSuccess", repos)
            executeNode(caseWrappedWrappedSuccess, repos, postInv) shouldBe true

            val caseWrappedDoubleSuccess = classDecl.extractMethodNode(postInv, "caseWrappedDoubleSuccess", repos)
            executeNode(caseWrappedDoubleSuccess, repos, postInv) shouldBe true

        }


        "$smt complexDataTypesParams"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypesparams.abs")))
            val classDecl = model.extractClassDecl("DTypesPar", "D")

            val parametricParamSuccess = classDecl.extractMethodNode(postInv, "parametricParamSuccess", repos)
            executeNode(parametricParamSuccess, repos, postInv) shouldBe true

            val caseReturnWrappedFuncSuccess = classDecl.extractMethodNode(postInv, "caseReturnWrappedFuncSuccess", repos)
            executeNode(caseReturnWrappedFuncSuccess, repos, postInv) shouldBe true

            val simpleOldSuccess = classDecl.extractMethodNode(postInv, "simpleOldSuccess", repos)
            executeNode(simpleOldSuccess, repos, postInv) shouldBe true

            val simpleOldFail = classDecl.extractMethodNode(postInv, "simpleOldFail", repos)
            executeNode(simpleOldFail, repos, postInv) shouldBe false

            val simpleLastSuccess = classDecl.extractMethodNode(postInv, "simpleLastSuccess", repos)
            executeNode(simpleLastSuccess, repos, postInv) shouldBe true

            val simpleLastFail = classDecl.extractMethodNode(postInv, "simpleLastFail", repos)
            executeNode(simpleLastFail, repos, postInv) shouldBe false

            val syncCallSuccess = classDecl.extractMethodNode(postInv, "syncCallSuccess", repos)
            executeNode(syncCallSuccess, repos, postInv) shouldBe true

            val whileSuccess = classDecl.extractMethodNode(postInv, "whileSuccess", repos)
            executeNode(whileSuccess, repos, postInv) shouldBe true

            val awaitWhileSuccess = classDecl.extractMethodNode(postInv, "awaitWhileSuccess", repos)
            executeNode(awaitWhileSuccess, repos, postInv) shouldBe true
        }

        "$smt functors"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/functors.abs")))
            val classDecl = model.extractClassDecl("Functors", "C")

            val trivialSuccess = classDecl.extractMethodNode(postInv, "trivialSuccess", repos)
            executeNode(trivialSuccess, repos, postInv) shouldBe true

            val caseSimpleSuccess = classDecl.extractMethodNode(postInv, "caseSimpleSuccess", repos)
            executeNode(caseSimpleSuccess, repos, postInv) shouldBe true

            val caseSimpleFail = classDecl.extractMethodNode(postInv, "caseSimpleFail", repos)
            executeNode(caseSimpleFail, repos, postInv) shouldBe false

            val caseFail = classDecl.extractMethodNode(postInv, "caseFail", repos)
            executeNode(caseFail, repos, postInv) shouldBe false

            val constFunctSuccess = classDecl.extractMethodNode(postInv, "constFunctSuccess", repos)
            executeNode(constFunctSuccess, repos, postInv) shouldBe true

            val varReturnSuccess = classDecl.extractMethodNode(postInv, "varReturnSuccess", repos)
            executeNode(varReturnSuccess, repos, postInv) shouldBe true

            val comparisonEqConstFunct = classDecl.extractMethodNode(postInv, "comparisonEqConstFunct", repos)
            executeNode(comparisonEqConstFunct, repos, postInv) shouldBe true

            val comparisonUneqConstFunct = classDecl.extractMethodNode(postInv, "comparisonUneqConstFunct", repos)
            executeNode(comparisonUneqConstFunct, repos, postInv) shouldBe true

            val whileSuccess = classDecl.extractMethodNode(postInv, "whileSuccess", repos)
            executeNode(whileSuccess, repos, postInv) shouldBe true

            val whileFuncInvSuccess = classDecl.extractMethodNode(postInv, "whileFuncInvSuccess", repos)
            executeNode(whileFuncInvSuccess, repos, postInv) shouldBe true

            val somethingSimpleFail = classDecl.extractMethodNode(postInv, "somethingSimpleFail", repos)
            executeNode(somethingSimpleFail, repos, postInv) shouldBe false

            val somethingSimpleSuccess = classDecl.extractMethodNode(postInv, "somethingSimpleSuccess", repos)
            executeNode(somethingSimpleSuccess, repos, postInv) shouldBe true

            val doubleFuncAppTrivialSuccess = classDecl.extractMethodNode(postInv, "doubleFuncAppTrivialSuccess", repos)
            executeNode(doubleFuncAppTrivialSuccess, repos, postInv) shouldBe true

            val doubleFuncAppTrivial2Success = classDecl.extractMethodNode(postInv, "doubleFuncAppTrivial2Success", repos)
            executeNode(doubleFuncAppTrivial2Success, repos, postInv) shouldBe true
        }

        "$smt functors_fields"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/functors.abs")))
            val classDecl = model.extractClassDecl("Functors", "D")

            val simpleOldSuccess = classDecl.extractMethodNode(postInv, "simpleOldSuccess", repos)
            executeNode(simpleOldSuccess, repos, postInv) shouldBe true

            val simpleOldFail = classDecl.extractMethodNode(postInv, "simpleOldFail", repos)
            executeNode(simpleOldFail, repos, postInv) shouldBe false

            val simpleLastSuccess = classDecl.extractMethodNode(postInv, "simpleLastSuccess", repos)
            executeNode(simpleLastSuccess, repos, postInv) shouldBe true

            val simpleLastFail = classDecl.extractMethodNode(postInv, "simpleLastFail", repos)
            executeNode(simpleLastFail, repos, postInv) shouldBe false

            val whileSuccess = classDecl.extractMethodNode(postInv, "whileSuccess", repos)
            executeNode(whileSuccess, repos, postInv) shouldBe true

            val somethingSimpleFail = classDecl.extractMethodNode(postInv, "somethingSimpleFail", repos)
            executeNode(somethingSimpleFail, repos, postInv) shouldBe false

            val somethingSimpleSuccess = classDecl.extractMethodNode(postInv, "somethingSimpleSuccess", repos)
            executeNode(somethingSimpleSuccess, repos, postInv) shouldBe true

            val doubleFuncAppTrivialSuccess = classDecl.extractMethodNode(postInv, "doubleFuncAppTrivialSuccess", repos)
            executeNode(doubleFuncAppTrivialSuccess, repos, postInv) shouldBe true
        }
        "$smt valueofDataTypes"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/valueofDataTypes.abs")))
            val classDecl = model.extractClassDecl("Values", "C")

            val iNode = classDecl.extractInitialNode(postInv)
            executeNode(iNode, repos, postInv) shouldBe true

            var sNode = classDecl.extractMethodNode(postInv,"success", repos)
            executeNode(sNode, repos, postInv) shouldBe true

            sNode = classDecl.extractMethodNode(postInv,"internal", repos)
            executeNode(sNode, repos, postInv) shouldBe true

            sNode = classDecl.extractMethodNode(postInv,"fail", repos)
            executeNode(sNode, repos, postInv) shouldBe false

            sNode = classDecl.extractMethodNode(postInv,"callOneOnThis", repos)
            executeNode(sNode, repos, postInv) shouldBe true
        }
    }
})