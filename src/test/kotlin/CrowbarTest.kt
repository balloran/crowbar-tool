import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.interfaces.runCommand
import org.abs_models.crowbar.types.PostInvType

open class CrowbarTest() : StringSpec() {

    val postInv = PostInvType::class
    val cvc: String = System.getenv("CVC") ?: "cvc"
    val z3: String = System.getenv("Z3") ?: "z3"
    fun backendAvailable(smt: String) : Boolean{
        val str = "$smt --help".runCommand()
        if(str == null) println("Backend $smt not found")
        return str != null
    }
}