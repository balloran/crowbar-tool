import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class DatatypeTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")
        smtPath = smt

        "$smt simpleDataTypes"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "C", repos)

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
        }

        "$smt mixedHeapsTest"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "D", repos)

            val mixedHeapSuccess = classDecl.extractMethodNode(postInv, "mixedHeapSuccess", repos)
            executeNode(mixedHeapSuccess, repos, postInv) shouldBe true

            val awaitSuccess = classDecl.extractMethodNode(postInv, "awaitSuccess", repos)
            executeNode(awaitSuccess, repos, postInv) shouldBe true

            val awaitWhileSuccess = classDecl.extractMethodNode(postInv, "awaitWhileSuccess", repos)
            executeNode(awaitWhileSuccess, repos, postInv) shouldBe true

        }

        "$smt dTypeFuncTest"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "D", repos)

            val trivialFuncSuccess = classDecl.extractMethodNode(postInv, "trivialFuncSuccess", repos)
            executeNode(trivialFuncSuccess, repos, postInv) shouldBe true

            val caseReturnFunc = classDecl.extractMethodNode(postInv, "caseReturnFunc", repos)
            executeNode(caseReturnFunc, repos, postInv) shouldBe true

        }
    }
})