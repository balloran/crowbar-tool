import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class DesugaringTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")

        "$smt desugaring"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/desugaring.abs")))
            val classDecl = model.extractClassDecl("Desugaring", "DesugaringC", repos)

            val simpleDesugaringSuccess = classDecl.extractMethodNode(postInv,"simpleDesugaringSuccess", repos)
            executeNode(simpleDesugaringSuccess, repos, postInv) shouldBe true

            val simpleDesugaringFail = classDecl.extractMethodNode(postInv,"simpleDesugaringFail", repos)
            executeNode(simpleDesugaringFail, repos, postInv) shouldBe false

            val desugaringPartiallyInheritedFail = classDecl.extractMethodNode(postInv,"desugaringPartiallyInheritedFail", repos)
            executeNode(desugaringPartiallyInheritedFail, repos, postInv) shouldBe false

            val desugaringFullyInheritedFail = classDecl.extractMethodNode(postInv,"desugaringFullyInheritedFail", repos)
            executeNode(desugaringFullyInheritedFail, repos, postInv) shouldBe true
        }

    }
})