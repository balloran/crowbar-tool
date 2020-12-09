import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class PostInvFuncTest : StringSpec({
	val postInv = PostInvType::class
	val cvc: String = System.getenv("CVC") ?: "cvc"
	val z3: String = System.getenv("Z3") ?: "z3"
	for (smt in listOf(z3, cvc)) {
		println("testing with: $smt as backend")
		
		"$smt basic1"{
			smtPath = smt
			val (model, repos) = load(listOf(Paths.get("src/test/resources/functionsbasic.abs")))
			var funcDecl = model.extractFunctionDecl("M", "mult", repos)
			var mNode = funcDecl.exctractFunctionNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true

			funcDecl = model.extractFunctionDecl("M", "multFail", repos)
			mNode = funcDecl.exctractFunctionNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe false

			funcDecl = model.extractFunctionDecl("M", "fac", repos)
			mNode = funcDecl.exctractFunctionNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true

			funcDecl = model.extractFunctionDecl("M", "facFail", repos)
			mNode = funcDecl.exctractFunctionNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe false

			val classDecl = model.extractClassDecl("M", "C", repos)

			mNode = classDecl.extractMethodNode(postInv,"m", repos)
			executeNode(mNode, repos, postInv) shouldBe true
			mNode = classDecl.extractMethodNode(postInv,"mFail", repos)
			executeNode(mNode, repos, postInv) shouldBe false
			mNode = classDecl.extractMethodNode(postInv,"mFailCall", repos)
			executeNode(mNode, repos, postInv) shouldBe false

		}
	}
})