import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.extractClassDecl
import org.abs_models.crowbar.main.extractMethodNode
import org.abs_models.crowbar.main.load
import org.abs_models.crowbar.main.smtPath
import org.abs_models.crowbar.tree.StaticNode
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class ContextTest : StringSpec( {
	val postInv = PostInvType::class
	val cvc: String = System.getenv("CVC") ?: "cvc"
	val z3: String = System.getenv("Z3") ?: "z3"
	for (smt in listOf(z3, cvc))
	{
		println("testing with: $smt as backend")
		smtPath = smt

		"$smt context"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/context.abs")))
			val classDecl = model.extractClassDecl("Context", "C", repos)
			classDecl.extractMethodNode(postInv, "m1", repos).collectInferenceLeaves().filterIsInstance<StaticNode>().size shouldBe 2
			classDecl.extractMethodNode(postInv, "m2", repos).collectInferenceLeaves().filterIsInstance<StaticNode>().size shouldBe 2
			classDecl.extractMethodNode(postInv, "m3", repos).collectInferenceLeaves().filterIsInstance<StaticNode>().size shouldBe 2
			classDecl.extractMethodNode(postInv, "m4", repos).collectInferenceLeaves().filterIsInstance<StaticNode>().size shouldBe 2
			classDecl.extractMethodNode(postInv, "m5", repos).collectInferenceLeaves().filterIsInstance<StaticNode>().size shouldBe 0
			classDecl.extractMethodNode(postInv, "m6", repos).collectInferenceLeaves().filterIsInstance<StaticNode>().size shouldBe 0
		}
	}
})