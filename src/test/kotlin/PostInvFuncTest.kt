import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class PostInvFuncTest : CrowbarTest() {
	init {
		for (smt in listOf(z3, cvc)){
			if (!backendAvailable(smt)) continue
			println("testing with $smt as backend")

			"$smt basic1"{
				smtPath = smt
				val (model, repos) = load(listOf(Paths.get("src/test/resources/functionsbasic.abs")))
				var funcDecl = model.extractFunctionDecl("M", "mult")
				var mNode = funcDecl.extractFunctionNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true

				funcDecl = model.extractFunctionDecl("M", "multFail")
				mNode = funcDecl.extractFunctionNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe false

				funcDecl = model.extractFunctionDecl("M", "fac")
				mNode = funcDecl.extractFunctionNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true

				funcDecl = model.extractFunctionDecl("M", "facFail")
				mNode = funcDecl.extractFunctionNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe false

				val classDecl = model.extractClassDecl("M", "C")

				mNode = classDecl.extractMethodNode(postInv, "m", repos)
				executeNode(mNode, repos, postInv) shouldBe true
				mNode = classDecl.extractMethodNode(postInv, "mFail", repos)
				executeNode(mNode, repos, postInv) shouldBe false
				mNode = classDecl.extractMethodNode(postInv, "mFailCall", repos)
				executeNode(mNode, repos, postInv) shouldBe false

			}
		}
	}
}