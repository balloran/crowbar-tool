
import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
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

        "matching-1" {
            val exp1 = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*(true)).skip.role!d(true)).role!e(true)")
            assert(exp1.matches(LTPatternCall("a")))
            assert(exp1.matches(LTPatternCall("c")))
            assert(exp1.matches(LTPatternCall("d")))
            assert(exp1.matches(LTPatternRep))
            assert(!exp1.matches(LTPatternCall("b")))
            assert(!exp1.matches(LTPatternCall("e")))
        }

        "matching-2" {
            val exp2 = LocalTypeParser.parse("(skip + Get(a)).Susp(true).(Put(true))*(true)")
            assert(exp2.matches(LTPatternGet))
            assert(exp2.matches(LTPatternSusp))
            assert(!exp2.matches(LTPatternPut))
            assert(!exp2.matches(LTPatternRep))
        }

        "transform" {
            var exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*(true)).skip.role!d(true).role!e(true)")
            exp = exp.readTransform(LTPatternCall("a"))
            exp = exp.readTransform(LTPatternCall("b"))
            exp = exp.readTransform(LTPatternCall("d"))
            exp = exp.readTransform(LTPatternCall("e"))
            exp shouldBe LTSkip

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*(true)).skip.role!d(true).role!e(true)")
            exp = exp.readTransform(LTPatternCall("c"))
            exp = exp.readTransform(LTPatternCall("c"))
            exp = exp.readTransform(LTPatternCall("c"))
            exp = exp.readTransform(LTPatternCall("d"))
            exp = exp.readTransform(LTPatternCall("e"))
            exp shouldBe LTSkip

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*(true)).skip.role!d(true).role!e(true)")
            exp = exp.readTransform(LTPatternCall("d"))
            exp = exp.readTransform(LTPatternCall("e"))
            exp shouldBe LTSkip
        }

        "transform-fail" {
            var exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*(true)).skip.role!d(true).role!e(true)")
            exp = exp.readTransform(LTPatternCall("a"))
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("c")) }

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*(true)).skip.role!d(true).role!e(true)")
            exp = exp.readTransform(LTPatternCall("c"))
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("a")) }
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("e")) }
        }
    }
}