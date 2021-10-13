import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class ExceptionTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"

    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")
        "$smt basic exception"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/except.abs")))
            val classDecl = model.extractClassDecl("M", "C")

            var res = classDecl.extractMethodNode(postInv, "success1", repos)
            executeNode(res, repos, postInv) shouldBe true
            res = classDecl.extractMethodNode(postInv, "success2", repos)
            executeNode(res, repos, postInv) shouldBe true
            res = classDecl.extractMethodNode(postInv, "success3", repos)
            executeNode(res, repos, postInv) shouldBe true
            for (i in 1..4) {
                res = classDecl.extractMethodNode(postInv, "fail$i", repos)
                executeNode(res, repos, postInv) shouldBe false
            }
        }
    }
})
