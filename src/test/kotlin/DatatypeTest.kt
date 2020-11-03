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
        }

        "$smt mixedHeapsTest"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/mixedheaps.abs")))
            val classDecl = model.extractClassDecl("MHeaps", "C", repos)

            val simpleSuccess = classDecl.extractMethodNode(postInv, "simpleSuccess", repos)
            executeNode(simpleSuccess, repos, postInv) shouldBe true

        }
    }
})