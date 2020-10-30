import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class DatatypeTest : StringSpec({
    val postInv = PostInvType::class
//    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3)) {
        println("testing with: $smt as backend")
        smtPath = smt

        "$smt simpleDataTypes"{
            val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
            val classDecl = model.extractClassDecl("DTypes", "C", repos)

            val trivialSuccess = classDecl.extractMethodNode(postInv,"caseSimpleSuccess", repos)
            executeNode(trivialSuccess, repos, postInv) shouldBe true

            val incrSuccess = classDecl.extractMethodNode(postInv,"caseSimpleFail", repos)
            executeNode(incrSuccess, repos, postInv) shouldBe false

            val trivialFail = classDecl.extractMethodNode(postInv,"caseFail", repos)
            executeNode(trivialFail, repos, postInv) shouldBe false
        }
    }
})