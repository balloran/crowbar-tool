package org.abs_models.crowbar.data

/**
 *  These are the structure to represent abstract programs, the calculus itself will be in AbstractType.kt.
 *  The parser is in AbstractParser.kt.
 */

/**
 *  Abstract represents anything in an abstract specification.
 */

interface Abstract : Anything

/**
 *  AESpec represents a constraint of an abstract specification.
 */

interface AESpec : Abstract

/**
 *  AEGlobal represents one global specification of an abstract specification.
 */

interface AEGlobal : AESpec

/**
 *  AEVarDec represents the declaration of locsets or formula of an abstract specification
 */

interface AEVarDec : AEGlobal

class AELocDec(val terms : List<AELoc>) : AEVarDec{

    override fun prettyPrint(): String {
        return "ae_specvars locset ${terms.map { term -> term.prettyPrint() }}"
    }

    override fun toString(): String {
        return "AELocDec($terms)"
    }
}

class AEForDec(val terms : List<AEPhiDec>) : AEVarDec{

    override fun prettyPrint(): String {
        return "ae_specvars formula ${terms.map { term -> term.prettyPrint() }}"
    }

    override fun toString(): String {
        return "AEForDec($terms)"
    }
}

/**
 *  AEConDec represents one global constraint of an abstract specification
 */

interface AEConDec : AEGlobal

class AEDis(val terms : List<AELoc>) : AEConDec{

    override fun prettyPrint(): String {
        return "ae_constraint disjoint ${terms.map { term -> term.prettyPrint() }}"
    }

    override fun toString(): String {
        return "AEDis($terms)"
    }
}

class AEMut(val terms : List<AEPhi>) : AEConDec{

    override fun prettyPrint(): String {
        return "ae_constraint mutex ${terms.map { term -> term.prettyPrint() }}"
    }

    override fun toString(): String {
        return "AEMut($terms)"
    }
}

/**
 *  AELocal represents a local constraint of an abstract specification.
 */

interface AELocal : AESpec

class AEStatement(val name : String) : AELocal{

    override fun prettyPrint(): String {
        return "abstract_statement $name"
    }

    override fun toString(): String {
        return "AEStatement($name)"
    }
}

class AEExpression(val name : String) : AELocal{

    override fun prettyPrint(): String {
        return "abstract_expression $name"
    }

    override fun toString(): String {
        return "AEExpression($name)"
    }
}

class AEAssignable(val id_locs : List<AELoc>) : AELocal{

    override fun prettyPrint(): String {
        return "assignable ${id_locs.map { loc -> loc.prettyPrint()}}"
    }

    override fun toString(): String {
        return "AEAssignable($id_locs)"
    }
}

class AEAccessible(val id_locs : List<AELoc>) : AELocal{

    override fun prettyPrint(): String {
        return "accessible ${id_locs.map { loc -> loc.prettyPrint()}}"
    }

    override fun toString(): String {
        return "AEAccessible($id_locs)"
    }
}

/**
 *  This interface regroups all the local behavior specification
 */

interface AEBehavior : AELocal

class AERetBehavior(val phi : AEPhi) : AEBehavior{

    override fun prettyPrint(): String {
        return "return_behavior requires ${phi.prettyPrint()}"
    }

    override fun toString(): String {
        return "AERetBehavior($phi)"
    }
}

class AENormBehavior(val phi : AEPhi) : AEBehavior{

    override fun prettyPrint(): String {
        return "normal_behavior requires ${phi.prettyPrint()}"
    }

    override fun toString(): String {
        return "AENormBehavior($phi)"
    }
}

/**
 *  AETerm stores terms of abstract specifications which can be abstract locations or formulas (phi) declarations.
 */

interface AETerm : Abstract

class AEPhiDec(val id_formula : String) : AETerm{

    override fun prettyPrint(): String {
        return "$id_formula(any)"
    }

    override fun toString(): String {
        return "AEPhiDec($id_formula)"
    }
}

/**
 *  AEPhi represents formula (phi) of abstract specifications.
 */

interface AEPhi : Abstract

data class AEInstantiatedPhi(val id_formula : String, val id_loc: String) : AEPhi{

    override fun prettyPrint(): String {
        return "$id_formula($id_loc)"
    }

    override fun toString(): String {
        return "AEInstantiatedPhi($id_formula, $id_loc)"
    }
}

data class AENot(val phi : AEPhi) : AEPhi{

    override fun prettyPrint(): String {
        return "not(${phi.prettyPrint()})"
    }

    override fun toString(): String {
        return "AENot($phi)"
    }
}

data class AEImpl(val ante : AEPhi, val succ : AEPhi) : AEPhi{

    override fun prettyPrint(): String {
        return "(${ante.prettyPrint()} -> ${succ.prettyPrint()})"
    }

    override fun toString(): String {
        return "AEImpl($ante, $succ)"
    }
}

data class AEAnd(val left : AEPhi, val right : AEPhi) : AEPhi{

    override fun prettyPrint(): String {
        return "(${left.prettyPrint()} and ${right.prettyPrint()})"
    }

    override fun toString(): String {
        return "(AEAnd($left, $right)"
    }
}

data class AEOr(val left : AEPhi, val right : AEPhi) :AEPhi{

    override fun prettyPrint(): String {
        return "(${left.prettyPrint()} or ${right.prettyPrint()})"
    }

    override fun toString(): String {
        return "AEOr($left, $right)"
    }
}

object AETrue : AEPhi{

    override fun prettyPrint(): String {
        return "true"
    }

    override fun toString(): String {
        return "AETrue"
    }
}

object AEFalse : AEPhi{

    override fun prettyPrint(): String {
        return "false"
    }

    override fun toString(): String {
        return "AEFalse"
    }
}

/**
 *  AELoc represents locations in abstract specifications.
 */

interface AELoc : AETerm{
    fun getName() : String
}

class AEInstantiatedLoc(val id_loc : String) : AELoc{

    override fun getName(): String = id_loc

    override fun prettyPrint(): String {
        return id_loc
    }

    override fun toString(): String {
        return "AEInstantiatedLoc($id_loc)"
    }
}

class AEHasToLoc(val loc: AELoc) : AELoc{

    override fun getName(): String = loc.getName()

    override fun prettyPrint(): String {
        return "hasTo(${loc.prettyPrint()})"
    }

    override fun toString(): String {
        return "AEHasToLoc($loc)"
    }
}

object AEEverything : AELoc{

    override fun getName(): String = "everything"

    override fun prettyPrint(): String {
        return "everything"
    }

    override fun toString(): String {
        return "AEEverything"
    }
}

object AENothing : AELoc{

    override fun getName(): String = "nothing"

    override fun prettyPrint(): String {
        return "nothing"
    }

    override fun toString(): String {
        return "AENothing"
    }
}


