import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class ExceptionTest : CrowbarTest() {
    init {
        for (smt in listOf(z3, cvc)){
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")
            "$smt basic exception"{
                smtPath = smt
                val (model, repos) = load(listOf(Paths.get("src/test/resources/except.abs")))
                val classDecl = model.extractClassDecl("M", "C")

                var res: SymbolicNode?
                for (i in 1..4) {
                    res = classDecl.extractMethodNode(postInv, "success$i", repos)
                    executeNode(res, repos, postInv) shouldBe true
                }
                for (i in 1..5) {
                    res = classDecl.extractMethodNode(postInv, "fail$i", repos)
                    executeNode(res, repos, postInv) shouldBe false
                }
            }
        }
    }
}
