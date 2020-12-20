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

	fun getSMTDType(dType : String) : HeapDecl = dtypeMap[libPrefix(dType)]!!
	fun getDeclForType(dType: String) : DataTypeDecl = dTypesDecl.find{ it.qualifiedName == dType }!!

	fun getAllTypePrefixes() : Set<String> = dtypeMap.keys

	override fun toString() : String {
		var header = DataTypesDecl(dTypesDecl).toSMT(true)
		for (dtype in dtypeMap)
			header += dtype.value.toSMT(true)
		return header
	}

	fun init(types:List<Type>){
		dtypeMap.clear()
		dTypesDecl.clear()
		for(type in types)
			dtypeMap[libPrefix(type.qualifiedName)] = HeapDecl(libPrefix(type.qualifiedName), listOf())

	}
	fun init(model: Model){
		init(listOf(model.intType))
		for(moduleDecl in model.moduleDecls){
			if(moduleDecl.name.startsWith("ABS.")) continue
			for(decl in moduleDecl.decls){
				if(decl is DataTypeDecl && decl.name != "Spec"){
					val datatypesConstList = mutableListOf<DataConstructor>()
					dTypesDecl.add(decl)
					for(constructor in decl.dataConstructorList){
						datatypesConstList.add(constructor)
					}
					dtypeMap[decl.qualifiedName] = HeapDecl(decl.type.qualifiedName, datatypesConstList.map { it.qualifiedName })
				}
			}
		}

	}
	fun libPrefix(type : String) : String {

		if(type=="ABS.StdLib.Fut"
				|| type=="ABS.StdLib.Bool"
				|| type.startsWith("Reference.")
				|| !dtypeMap.containsKey(type))
			return "Int"
		return type.removePrefix("ABS.StdLib.")
	}

}

object FunctionRepos{
    private val known : MutableMap<String, FunctionDecl> = mutableMapOf()
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
					val transpost = funpost.toSMT(true).replace("result","($name $callParams)")
					val nextDef = "\n(assert (forall ($paramsTyped) (=> ${funpre.toSMT(true)} $transpost)))"
					defs += nextDef
				}else{
					val transpost = funpost.toSMT(true).replace("result","$name ")
					val nextDef = "\n(assert  (=> ${funpre.toSMT(true)} $transpost))"
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
				    sigs += "\t(${pair.key.replace(".", "-")} (${params.fold("", { acc, nx -> "$acc (${nx.name} Int)" })}) Int)\n"
				    defs += "\t${exprToTerm(translateABSExpToSymExpr(def, "<UNKNOWN>")).toSMT(false)}\n"
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
		if(params.find { !repos.isAllowedType(it.type.qualifiedName) } != null){
			System.err.println("functions with non-Int type not supported")
			exitProcess(-1)
		}
		val fType = fDecl.type
		if(!repos.isAllowedType(fType.qualifiedName)) {
			System.err.println("parameters with non-Int type not supported")
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