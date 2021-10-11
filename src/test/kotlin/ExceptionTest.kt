import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class ExceptionTest : StringSpec({
    val postInv = PostInvType::class

        "basic exception"{
            smtPath = System.getenv("Z3") ?: "z3"
            val (model, repos) = load(listOf(Paths.get("src/test/resources/except.abs")))
            val classDecl = model.extractClassDecl("M", "C")

            var res = classDecl.extractMethodNode(postInv, "success1", repos)
            executeNode(res, repos, postInv) shouldBe true
            for(i in 1..3) {
                res = classDecl.extractMethodNode(postInv, "fail$i", repos)
                executeNode(res, repos, postInv) shouldBe false
            }
        }
})
