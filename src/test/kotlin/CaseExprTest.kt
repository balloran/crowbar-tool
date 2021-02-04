import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths
import kotlin.system.exitProcess

class CaseExprTest : StringSpec({
    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    for (smt in listOf(z3, cvc)) {
        println("testing with: $smt as backend")


        "$smt caseExp"{
            smtPath = smt

            val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
            val classDecl = model.extractClassDecl("CaseExpr", "E", repos)

            val fullIntSuccess = classDecl.extractMethodNode(postInv, "fullIntSuccess", repos)
            executeNode(fullIntSuccess, repos, postInv) shouldBe true

            val intParamTypeReturnSuccess = classDecl.extractMethodNode(postInv, "intParamTypeReturnSuccess", repos)
            executeNode(intParamTypeReturnSuccess, repos, postInv) shouldBe true

            val constMatchFullTypeSuccess = classDecl.extractMethodNode(postInv, "constMatchFullTypeSuccess", repos)
            executeNode(constMatchFullTypeSuccess, repos, postInv) shouldBe true

            val complexTypeMatchSuccess = classDecl.extractMethodNode(postInv, "complexTypeMatchSuccess", repos)
            executeNode(complexTypeMatchSuccess, repos, postInv) shouldBe true

            val functorUsageSuccess = classDecl.extractMethodNode(postInv, "functorUsageSuccess", repos)
            executeNode(functorUsageSuccess, repos, postInv) shouldBe true

            val assignmentCaseExprSuccess = classDecl.extractMethodNode(postInv, "assignmentCaseExprSuccess", repos)
            executeNode(assignmentCaseExprSuccess, repos, postInv) shouldBe true
        }

        "$smt patternMatching"{
            smtPath = smt
            val (model, repos) = load(listOf(Paths.get("src/test/resources/caseExpr.abs")))
            val classDecl = model.extractClassDecl("CaseExpr", "E", repos)

            val patternMatchingIntTrivialType3Success = classDecl.extractMethodNode(postInv, "patternMatchingIntTrivialType3Success", repos)
            executeNode(patternMatchingIntTrivialType3Success, repos, postInv) shouldBe true

            val patternMatchingFunctorSuccess = classDecl.extractMethodNode(postInv, "patternMatchingFunctorSuccess", repos)
            executeNode(patternMatchingFunctorSuccess, repos, postInv) shouldBe true

            val patternMatchingTypeTrivialType3Success = classDecl.extractMethodNode(postInv, "patternMatchingTypeTrivialType3Success", repos)
            executeNode(patternMatchingTypeTrivialType3Success, repos, postInv) shouldBe true

            val patternMatchingWrapTypeFirstBranchSuccess = classDecl.extractMethodNode(postInv, "patternMatchingWrapTypeFirstBranchSuccess", repos)
            executeNode(patternMatchingWrapTypeFirstBranchSuccess, repos, postInv) shouldBe true

            val patternMatchingDoubleWrapTypeFirstBranchSuccess = classDecl.extractMethodNode(postInv, "patternMatchingDoubleWrapTypeFirstBranchSuccess", repos)
            executeNode(patternMatchingDoubleWrapTypeFirstBranchSuccess, repos, postInv) shouldBe true

            val patternMatchingDoubleWrapTypeFirstBranchFail = classDecl.extractMethodNode(postInv, "patternMatchingDoubleWrapTypeFirstBranchFail", repos)
            executeNode(patternMatchingDoubleWrapTypeFirstBranchFail, repos, postInv) shouldBe false

            val patternMatchingFuncMatchSuccess = classDecl.extractMethodNode(postInv, "patternMatchingFuncMatchSuccess", repos)
            executeNode(patternMatchingFuncMatchSuccess, repos, postInv) shouldBe true
        }
    }
})