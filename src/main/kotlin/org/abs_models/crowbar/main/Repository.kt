package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.interfaces.*
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.Type
import kotlin.reflect.KClass
import kotlin.system.exitProcess


object ADTRepos {

	private val dtypeMap: MutableMap<String,  HeapDecl> = mutableMapOf()
	val dTypesDecl = mutableListOf<DataTypeDecl>()
	private val usedHeaps = mutableSetOf<String>()
	private val stdLibTypes = mutableSetOf<String>()


	fun setUsedHeaps(usedHeapsPar : Set<String>) {
		usedHeaps.clear()
		usedHeaps.addAll(usedHeapsPar)
	}

	fun getSMTDType(dType : String) : HeapDecl = dtypeMap[libPrefix(dType)]!!
	fun getDeclForType(dType: String) : DataTypeDecl = dTypesDecl.find{ it.qualifiedName == dType }!!

	fun getAllTypePrefixes() : Set<String> = dtypeMap.keys
	fun getUsedTypePrefixes() : Set<String> = usedHeaps

	override fun toString() : String {
		var header = DataTypesDecl(dTypesDecl).toSMT()
		for (dtype in dtypeMap) {

			header +=
				if(!conciseProofs || dtype.key in usedHeaps)
					dtype.value.toSMT()
				else
					"\n; no fields of type ${dtype.key}: omitting declaration of ${dtype.value.heapType}"

		}
		return header
	}

	fun initStdLib(){
		dtypeMap.clear()
		dTypesDecl.clear()
		dtypeMap["Int"] = HeapDecl("Int")
		dtypeMap["Bool"] = HeapDecl("Bool")
	}
	fun init(model: Model){
		initStdLib()
		for(moduleDecl in model.moduleDecls){
			if(moduleDecl.name.startsWith("ABS.")) continue
			for(decl in moduleDecl.decls){
				if(decl is DataTypeDecl && decl.name != "Spec"){
					dTypesDecl.add(decl)
					dtypeMap[decl.qualifiedName] = HeapDecl(decl.type.qualifiedName)
				}
			}
		}

	}
	fun libPrefix(type: String): String {
		return when {
			type == "ABS.StdLib.Bool" -> "Bool"
			dtypeMap.containsKey(type) -> type
			else -> "Int"
		}
	}

}

object FunctionRepos{
    val known : MutableMap<String, FunctionDecl> = mutableMapOf()


    fun isKnown(str: String) = known.containsKey(str)
    fun get(str: String) = known.getValue(str)
	fun hasContracts() = known.filter { hasContract(it.value) }.any()
	fun contracts() = known.filter { hasContract(it.value) }
    override fun toString() : String {
	    val contracts = contracts()
	    val direct = known.filter { !hasContract(it.value) }
	    var ret = ""

		if(contracts.isNotEmpty()) {
		    var sigs = ""
		    var defs = ""
		    for (pair in contracts) {
			    val name = pair.key.replace(".", "-")
			    val params = pair.value.params
			    val zParams = params.joinToString(" ") { ADTRepos.libPrefix(it.type.qualifiedName) }

			    val nextsig =  "\n(declare-fun $name ($zParams) ${ADTRepos.libPrefix(pair.value.type.qualifiedName)})" //todo: use interface to get SMT declaration
			    sigs += nextsig

			    val callParams = params.joinToString(" ") { it.name }

			    val funpre = extractSpec(pair.value, "Requires", pair.value.type.qualifiedName)
			    val funpost = extractSpec(pair.value, "Ensures", pair.value.type.qualifiedName)

				val paramsTyped = params.joinToString(" ") { "(${it.name} ${ADTRepos.libPrefix(it.type.qualifiedName)})" }
				if(params.count() > 0) {
					val transpost = funpost.toSMT().replace("result","($name $callParams)")
					val nextDef = "\n(assert (forall ($paramsTyped) (=> ${funpre.toSMT()} $transpost)))"
					defs += nextDef
				}else{
					val transpost = funpost.toSMT().replace("result","$name ")
					val nextDef = "\n(assert  (=> ${funpre.toSMT()} $transpost))"
					defs += nextDef
				}

		    }
		    ret += (sigs+defs)
	    }
		    if(direct.isNotEmpty()) {
			    var sigs = ""
			    var defs = ""
			    for (pair in direct) {
				    val params = pair.value.params
				    val eDef: ExpFunctionDef = pair.value.functionDef as ExpFunctionDef
				    val def = eDef.rhs
					sigs += "\t(${pair.key.replace(".", "-")} (${params.fold("",{ acc, nx -> "$acc (${nx.name} ${ADTRepos.libPrefix(nx.type.qualifiedName)})" })})  ${ADTRepos.libPrefix(def.type.qualifiedName)})\n"
					defs += "\t${exprToTerm(translateABSExpToSymExpr(def, "<UNKNOWN>")).toSMT()}\n"
			    }
				ret += "\n(define-funs-rec(\n$sigs)(\n$defs))"
		    }
	    return ret
    }

	private fun hasContract(fDecl: FunctionDecl) : Boolean {
		return fDecl.annotationList.filter { it.type.toString().endsWith(".Spec") }.any()
	}


	fun init(model: Model, repos: Repository) {
		known.clear()
		for (mDecl in model.moduleDecls){
			if(mDecl.name.startsWith("ABS.")) continue
			for (decl in mDecl.decls){
				if(decl is FunctionDecl){
					initFunctionDef(decl, repos)
				}
			}
		}
	}

	private fun initFunctionDef(fDecl: FunctionDecl, repos: Repository) {
		val fName = fDecl.qualifiedName
		val params = fDecl.params
		if(params.find { !repos.isAllowedType(it.type.toString()) && !repos.isAllowedType(it.type.toString()) } != null){
			System.err.println("functions with not supported types: ${params.map { it.type }}")

			exitProcess(-1)
		}
		val fType = fDecl.type
		if(!repos.isAllowedType(fType.toString())) {
			System.err.println("parameters with not supported type: $fType")
			exitProcess(-1)
		}
		if(fDecl.functionDef is ExpFunctionDef){
			known[fName] = fDecl
		} else {
			System.err.println("builtin types not supported")
			exitProcess(-1)
		}
	}
	fun extractAll(usedType: KClass<out DeductType>) : List<Pair<String,SymbolicNode>> {
		return known.filter { hasContract(it.value) }.map { Pair(it.key,it.value.exctractFunctionNode(usedType)) }
	}
}