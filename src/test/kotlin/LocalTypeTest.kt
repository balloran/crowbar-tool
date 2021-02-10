
import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.LocalTypeParser

class LocalTypeTest : StringSpec() {

    init {
        "matching-1" {
            val exp1 = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true)).role!e(true)", null)
            assert(exp1.matches(LTPatternCall("a")))
            assert(exp1.matches(LTPatternCall("c")))
            assert(exp1.matches(LTPatternCall("d")))
            assert(exp1.matches(LTPatternRep))
            assert(!exp1.matches(LTPatternCall("b")))
            assert(!exp1.matches(LTPatternCall("e")))
        }

        "matching-2" {
            val exp2 = LocalTypeParser.parse("(skip + Get(a)).Susp(true).(Put(true))*", null)
            assert(exp2.matches(LTPatternGet))
            assert(exp2.matches(LTPatternSusp))
            assert(!exp2.matches(LTPatternPut))
            assert(!exp2.matches(LTPatternRep))
        }

        "transform" {
            var exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("a"))
            exp = exp.readTransform(LTPatternCall("b"))
            exp = exp.readTransform(LTPatternCall("d"))
            exp = exp.readTransform(LTPatternCall("e"))
            exp shouldBe LTSkip

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("c"))
            exp = exp.readTransform(LTPatternCall("c"))
            exp = exp.readTransform(LTPatternCall("c"))
            exp = exp.readTransform(LTPatternCall("d"))
            exp = exp.readTransform(LTPatternCall("e"))
            exp shouldBe LTSkip

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("d"))
            exp = exp.readTransform(LTPatternCall("e"))
            exp shouldBe LTSkip
        }

        "transform-fail" {
            var exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("a"))
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("c")) }

            exp = LocalTypeParser.parse("(role!a(true).role!b(true) + (role!c(true))*).skip.role!d(true).role!e(true)", null)
            exp = exp.readTransform(LTPatternCall("c"))
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("a")) }
            shouldThrow<Exception>{ exp.readTransform(LTPatternCall("e")) }
        }
    }
}