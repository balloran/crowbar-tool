
import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.LocalTypeParser

class LocalTypeTest : StringSpec() {

    init {
        "parsing" {
            val testPairs = mapOf(
                "skip"                   to "skip",
                "Get(func(42, this.f2))" to "Get(func(42,this.f2 : <UNKNOWN>))",
                "Put(a && b || c)"       to "Put[((a=true) /\\ (b=true)) \\/ (c=true)]",
                "Susp(!this.f1)"         to "Susp[!this.f1 : <UNKNOWN>=true]",
                "role!m(this.f1 * someVar)" to "role!m[this.f1 : <UNKNOWN>*someVar=true]",
                "role!m(this.f1 + this.f2).Get(this.someField)" to "(role!m[this.f1 : <UNKNOWN>+this.f2 : <UNKNOWN>=true].Get(this.someField : <UNKNOWN>))",
                "Susp(true) + Put(true)"    to "(Susp[true=true] + Put[true=true])",
                "(Susp(true) + Put(true)).role!n(false)" to "(((Susp[true=true] + Put[true=true])).role!n[false=true])",
                "(role!m(true))*(true).Put(true)" to "((role!m[true=true])*[true=true].Put[true=true])"
            )

            testPairs.forEach {
                val parsed = LocalTypeParser.parse(it.key).prettyPrint()
                parsed shouldBe it.value
            }
        }
    }
}