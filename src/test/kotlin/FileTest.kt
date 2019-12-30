import io.kotlintest.data.forall
import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import io.kotlintest.specs.StringSpec
import io.kotlintest.tables.Row1
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class FileTest : StringSpec ({
	"success"{
		forall(Row1("z3"),
			   Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/success.abs")))
			val classDecl = model.extractClassDecl("Success", "C", repos)
			classDecl.executeAll(repos) shouldBe true
		}
	}
	"fails"{
		forall(Row1("z3"),
			   Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/fail.abs")))
			val classDecl = model.extractClassDecl("Fail", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe false

			for (m in classDecl.methods) {
				val node = classDecl.extractMethodNode(m.methodSig.name, repos)
				executeNode(node, repos) shouldBe false
			}
		}
	}
	"create"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/create.abs")))
			val classDecl = model.extractClassDecl("Create", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe true

			val sNode = classDecl.extractMethodNode("success", repos)
			executeNode(sNode, repos) shouldBe true

			val fNode = classDecl.extractMethodNode("fail", repos)
			executeNode(fNode, repos) shouldBe false

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe true
		}
	}
	"reference"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/reference.abs")))
			val classDecl = model.extractClassDecl("Reference", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe true

			val m1Node = classDecl.extractMethodNode("m1", repos)
			executeNode(m1Node, repos) shouldBe false

			val m2Node = classDecl.extractMethodNode("m2", repos)
			executeNode(m2Node, repos) shouldBe false //see comment in file

			val m3Node = classDecl.extractMethodNode("m3", repos)
			executeNode(m3Node, repos) shouldBe true

			val m4Node = classDecl.extractMethodNode("m4", repos)
			executeNode(m4Node, repos) shouldBe true

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe false
		}
	}
	"multi"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/multi1.abs"), Paths.get("src/test/resources/multi2.abs")))
			val classDecl = model.extractClassDecl("Multi1", "C", repos)
			classDecl.executeAll(repos) shouldBe true

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe true
		}
	}
	"typeerror"{
		shouldThrow<Exception> {
			load(listOf(Paths.get("src/test/resources/exception.abs")))
		}
	}
})