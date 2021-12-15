import io.kotlintest.shouldBe
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class CastingTest : CrowbarTest() {
    init {
        for (smt in listOf(z3, cvc)) {
            if (!backendAvailable(smt)) continue
            println("testing with $smt as backend")

            "$smt simpleCasting"{
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

                val inliningCastSimpleSuccess = classDecl.extractMethodNode(postInv, "inliningCastSimpleSuccess", repos)
                executeNode(inliningCastSimpleSuccess, repos, postInv) shouldBe true

                val extendsCastSimpleSuccess = classDecl.extractMethodNode(postInv, "extendsCastSimpleSuccess", repos)
                executeNode(extendsCastSimpleSuccess, repos, postInv) shouldBe true

                val castNullNoCallsSuccess = classDecl.extractMethodNode(postInv, "castNullNoCallsSuccess", repos)
                executeNode(castNullNoCallsSuccess, repos, postInv) shouldBe true

                val castNullCallOnNullReturnValFail =
                    classDecl.extractMethodNode(postInv, "castNullCallOnNullReturnValFail", repos)
                executeNode(castNullCallOnNullReturnValFail, repos, postInv) shouldBe false

            }

            "$smt objectCreation"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/casting.abs")))
                val classDecl = model.extractClassDecl("Casting", "C")

                val castCreatedObjectSimpleSuccess =
                    classDecl.extractMethodNode(postInv, "castCreatedObjectSimpleSuccess", repos)
                executeNode(castCreatedObjectSimpleSuccess, repos, postInv) shouldBe true


                val castCreatedObjectExtendsSuccess =
                    classDecl.extractMethodNode(postInv, "castCreatedObjectExtendsSuccess", repos)
                executeNode(castCreatedObjectExtendsSuccess, repos, postInv) shouldBe true

                val castCreatedObjectDifferentInterfaceSuccess =
                    classDecl.extractMethodNode(postInv, "castCreatedObjectDifferentInterfaceSuccess", repos)
                executeNode(castCreatedObjectDifferentInterfaceSuccess, repos, postInv) shouldBe true


            }
        }
    }
}