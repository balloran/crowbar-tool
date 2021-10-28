import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class CastingTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")

        "$smt caseExp"{
            smtPath = smt

            val (model, repos) = load(listOf(Paths.get("src/test/resources/casting.abs")))
            val classDecl = model.extractClassDecl("Casting", "C")

            val preSimpleSuccess = classDecl.extractMethodNode(postInv, "preSimpleSuccess", repos)
            executeNode(preSimpleSuccess, repos, postInv) shouldBe true

            val withoutPreSimpleFail1 = classDecl.extractMethodNode(postInv, "withoutPreSimpleFail1", repos)
            executeNode(withoutPreSimpleFail1, repos, postInv) shouldBe false

            val withoutPreSimpleFail2 = classDecl.extractMethodNode(postInv, "withoutPreSimpleFail2", repos)
            executeNode(withoutPreSimpleFail2, repos, postInv) shouldBe false

            val withoutPreSimpleFail3 = classDecl.extractMethodNode(postInv, "withoutPreSimpleFail3", repos)
            executeNode(withoutPreSimpleFail3, repos, postInv) shouldBe false

        }
    }


})