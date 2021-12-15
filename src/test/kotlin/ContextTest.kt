import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.extractClassDecl
import org.abs_models.crowbar.main.extractMethodNode
import org.abs_models.crowbar.main.load
import org.abs_models.crowbar.main.smtPath
import java.nio.file.Paths

class ContextTest : CrowbarTest() {
	init {
		for (smt in listOf(z3, cvc)){
			if (!backendAvailable(smt)) continue
			println("testing with $smt as backend")
			smtPath = smt

			"$smt context"{
				val (model, repos) = load(listOf(Paths.get("src/test/resources/context.abs")))
				val classDecl = model.extractClassDecl("Context", "C")
				classDecl.extractMethodNode(postInv, "m1", repos).collectInferenceLeaves().size shouldBe 2
				classDecl.extractMethodNode(postInv, "m2", repos).collectInferenceLeaves().size shouldBe 2
				classDecl.extractMethodNode(postInv, "m3", repos).collectInferenceLeaves().size shouldBe 2
				classDecl.extractMethodNode(postInv, "m4", repos).collectInferenceLeaves().size shouldBe 2
				classDecl.extractMethodNode(postInv, "m5", repos).collectInferenceLeaves().size shouldBe 0
				classDecl.extractMethodNode(postInv, "m6", repos).collectInferenceLeaves().size shouldBe 0
			}
		}
	}
}