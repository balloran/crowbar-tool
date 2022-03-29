package org.abs_models.crowbar.data

/**
 *  These file is currently in work.
 *  These are the structure to represent abstract programs, the calculus itself will be in AbstractType.kt.
 *  The parser is in AbstractParser.kt.
 */

/**
 *  Abstract represents anything in an abstract specification.
 */

interface Abstract : Anything{

}

/**
 *  AESpec represents a constraint of an abstract specification.
 */

interface AESpec : Abstract{

}

/**
 *  AEGlobal represents one global specification of an abstract specification.
 */

interface AEGlobal : AESpec{

}

/**
 *  AEVarDec represents the declaration of locsets or formula of an abstract specification
 */

interface AEVarDec : AEGlobal{

}

class AELocDec(val terms : List<AELoc>) : AEVarDec{

    override fun toString(): String {
        return "ae_specvars locset $terms"
    }
}

class AEForDec(val terms : List<AEPhiDec>) : AEVarDec{

    override fun toString(): String {
        return "ae_specvars formula $terms"
    }
}

/**
 *  AEConDec represents one global constraint of an abstract specification
 */

interface AEConDec : AEGlobal{

}

class AEDis(val terms : List<AELoc>) : AEConDec{

    override fun toString(): String {
        return "ae_constraint disjoint $terms"
    }
}

class AEMut(val terms : List<AEPhi>) : AEConDec{

    override fun toString(): String {
        return "ae_constraint mutex $terms"
    }
}

/**
 *  AELocal represents a local constraint of an abstract specification.
 */

class AELocal : AESpec{


}

/**
 *  AETerm stores terms of abstract specifications which can be abstract locations or formulas (phi).
 */

interface AETerm : Abstract{

}

class AEPhiDec(val id_formula : String) : AETerm{

    override fun toString(): String {
        return "$id_formula(any)"
    }
}

/**
 *  AEPhi represents formula (phi) of abstract specifications.
 */

interface AEPhi : AETerm{

}

class AEInstantiatedPhi(val id_formula : String, val id_loc: String) : AEPhi{

    override fun toString(): String {
        return "$id_formula($id_loc)"
    }
}

object AETrue : AEPhi{

    override fun toString(): String {
        return "true"
    }
}

object AEFalse : AEPhi{

    override fun toString(): String {
        return "false"
    }
}

/**
 *  AELoc represents locations in abstract specifications.
 */

interface AELoc : AETerm{

}

class AEInstantiatedLoc(val id_loc : String) : AELoc{

    override fun toString(): String {
        return "$id_loc"
    }
}

class AEHasToLoc(val loc: AELoc) : AELoc{

    override fun toString(): String {
        return "hasTo($loc)"
    }
}

object AEEverything : AELoc{

    override fun toString(): String {
        return "everything"
    }
}

object AENothing : AELoc{

    override fun toString(): String {
        return "nothing"
    }
}


