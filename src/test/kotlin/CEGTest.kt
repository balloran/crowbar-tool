
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.investigator.CounterexampleGenerator
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import org.abs_models.frontend.ast.ClassDecl
import java.nio.file.Paths

class CEGTest : StringSpec() {

    init {
        val cvc: String = System.getenv("CVC") ?: "cvc"
        val z3: String = System.getenv("Z3") ?: "z3"

        for (smt in listOf(z3, cvc)) {

            "$smt CEG case study demo"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/CEGcasestudy.abs")))
                val classDecl = model.extractClassDecl("CaseStudy", "Reader")

                attemptVerification(classDecl, "read", repos)
                attemptVerification(classDecl, "readAvg", repos)
                attemptVerification(classDecl, "divide", repos)
            }

            "$smt CEG data types"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypes.abs")))
                val classDecl = model.extractClassDecl("DTypes", "C")

                attemptVerification(classDecl, "caseSimpleFail", repos)
                attemptVerification(classDecl, "caseFail", repos)
                attemptVerification(classDecl, "ifExpFail", repos)
            }

            "$smt CEG parameter data types"{
                smtPath = smt

                val (model, repos) = load(listOf(Paths.get("src/test/resources/datatypesparams.abs")))
                var classDecl = model.extractClassDecl("DTypesPar", "C")

                attemptVerification(classDecl, "trivialFail", repos)
                attemptVerification(classDecl, "caseSimpleFail", repos)
                attemptVerification(classDecl, "caseWrappedFail", repos)

                classDecl = model.extractClassDecl("DTypesPar", "D")

                attemptVerification(classDecl, "simpleOldFail", repos)
                attemptVerification(classDecl, "simpleLastFail", repos)
            }
        }
    }
}

// No explicit assertions here because all we attempt to show is that the CEG doesn't crash
fun attemptVerification(classDecl: ClassDecl, method: String, repos: Repository) {
    // Enable investigator
    investigate = true
    // Do not actually write counterexamples to disk
    CounterexampleGenerator.dryrun = true

    val postInv = PostInvType::class
    val node = classDecl.extractMethodNode(postInv, method, repos)

    // The @AfterClass annotation seems to require some new dependencies
    // so we'll make do with this instead
    try {
        executeNode(node, repos, postInv)
    } finally {
        investigate = false
        CounterexampleGenerator.dryrun = false
    }
}