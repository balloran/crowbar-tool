package org.abs_models.crowbar.main

import org.abs_models.crowbar.data.*
import org.abs_models.crowbar.data.Function
import org.abs_models.crowbar.interfaces.*
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.crowbar.types.getReturnType
import org.abs_models.frontend.ast.*
import org.abs_models.frontend.typechecker.DataTypeType
import org.abs_models.frontend.typechecker.Type
import org.abs_models.frontend.typechecker.UnionType
import org.abs_models.frontend.typechecker.UnknownType
import kotlin.reflect.KClass
import kotlin.system.exitProcess

/**
 *   The structures in this file keep track of information from the AST that is not visible in the IR because it is outside of statement:
 *    - ADTRepos manages the data types
 *    - FunctionRepos manages the functional layer
 *    - Repository manages the specification
 */
object ADTRepos {

	var model:Model? = null

	private val dtypeMap: MutableMap<String, HeapDecl> = mutableMapOf()
	val dTypesDecl = mutableListOf<DataTypeDecl>()
	val primitiveDtypesDecl = mutableListOf<DataTypeDecl>()
	val exceptionDecl = mutableListOf<ExceptionDecl>()
	val interfaceDecl = mutableListOf<InterfaceDecl>()

	val objects : MutableMap<String,UnionType> = mutableMapOf()

	private val concreteGenerics :MutableMap<String, DataTypeType> = mutableMapOf()
	private val usedHeaps = mutableSetOf<String>()

	//These are either handled manually as special cases (e.g., float, Exception)
	private val ignorableBuiltInDataTypes : Set<String> = setOf(
			"ABS.StdLib.Map",
			"ABS.StdLib.Float",
			"ABS.StdLib.Time",
			"ABS.StdLib.Duration",
			"ABS.StdLib.Exception",
			"ABS.StdLib.Annotation",
			"ABS.StdLib.LocationType",
			"ABS.StdLib.NullableType",
			"ABS.StdLib.ClassKindAnnotation",
			"ABS.StdLib.FinalAnnotation",
			"ABS.StdLib.AtomicityAnnotation",
			"ABS.StdLib.ReadonlyAnnotation",
			"ABS.StdLib.HTTPCallableAnnotation")


	private fun addUsedHeap(heap :String){
		usedHeaps.add(heap)
	}

	fun setUsedHeaps(usedHeapsPar : Set<String>) {
		usedHeaps.clear()
		usedHeaps.addAll(usedHeapsPar)
	}

	private fun isBuildInType(type : Type) :Boolean{
		return type.isBoolType || type.isIntType
	}

	fun getSMTDType(dType : String) : HeapDecl =
		try {
			dtypeMap[libPrefix(dType)]!!
		}catch ( e:KotlinNullPointerException ){
			System.err.println("Type $dType not supported")
				exitProcess(-1)
		}
	fun getDeclForType(dType: String) : DataTypeDecl = dTypesDecl.find{ it.qualifiedName == dType }!!

	fun getAllTypePrefixes() : Set<String> = dtypeMap.keys
	fun getUsedTypePrefixes() : Set<String> = usedHeaps

	fun clearConcreteGenerics(){
		concreteGenerics.clear()
	}

	fun addGeneric(type : DataTypeType) {
		if(!type.typeArgs.any { it.isUnknownType }) {
			type.typeArgs.map {
				if (isBoundGeneric(it)) {
					addGeneric(it as DataTypeType)
				}
			}
			concreteGenerics[type.toString()] = type
			val heapName = genericTypeSMTName(type)
			dtypeMap[heapName] = HeapDecl(heapName)
			addUsedHeap(heapName)
		}
	}

	fun genericsToSMT() :String{
		val names = mutableListOf<ArgsSMT>()
		val decls = mutableListOf<ArgSMT>()
		val valueOf = mutableListOf<FunctionDeclSMT>()

		concreteGenerics.values.map{
			val map = (it.decl.type as DataTypeType).typeArgs.zip(it.typeArgs).toMap()
			val list = GenericTypeDecl(it.decl, map, it.typeArgs).getDecl()
			names.add(list[0] as ArgsSMT)
			decls.add(list[1] as ArgSMT)
			valueOf.add(list[2] as FunctionDeclSMT)
		}
		val decl = Function(
			"declare-datatypes", (
					listOf(ArgSMT(names), ArgSMT(decls))))
		return if(names.isNotEmpty())
			decl.toSMT() + "\n${valueOf.joinToString("") { it.toSMT("\n") }}"
		else
			""
	}

	fun heapsToSMT() :String{
		var header = ""
		for (dtype in dtypeMap) {

			header +=
				if(!conciseProofs || dtype.key in usedHeaps)
					dtype.value.toSMT()
				else
					"\n; no fields of type ${dtype.key}: omitting declaration of ${dtype.value.heapType}"

		}
		return header
	}

	fun interfaceExtendsToSMT() : String {
		var res = ""
		interfaceDecl.forEach { i1 ->
			i1.extendedInterfaceUseListNoTransform.forEach { i2 ->

				res += "(assert (extends ${i1.type.qualifiedName} ${i2.type.qualifiedName}))\n\t"
			}
		}
		return res
	}

	fun dTypesToSMT() :String{
		return DataTypesDecl(dTypesDecl, exceptionDecl,interfaceDecl).toSMT()
	}

	override fun toString() : String {
		return DataTypesDecl(dTypesDecl, exceptionDecl,interfaceDecl).toSMT()
	}

	fun initBuiltIn(){
		dtypeMap.clear()
		dTypesDecl.clear()
		primitiveDtypesDecl.clear()
		exceptionDecl.clear()
		interfaceDecl.clear()
		objects.clear()
		dtypeMap["ABS.StdLib.Int"] = HeapDecl("ABS.StdLib.Int")
		dtypeMap["ABS.StdLib.Float"] = HeapDecl("ABS.StdLib.Float")
	}
	fun init(parModel: Model){
		model = parModel
		initBuiltIn()
		for(moduleDecl in parModel.moduleDecls){

			if(moduleDecl.name.startsWith("ABS.")
				&& !moduleDecl.name.startsWith("ABS.StdLib")) continue
			for(decl in moduleDecl.decls){
				if(!moduleDecl.name.startsWith("ABS.StdLib.Exceptions") && decl is DataTypeDecl && decl.name != "Spec" && decl.qualifiedName !in ignorableBuiltInDataTypes){
					if(!isBuildInType(decl.type)) {
						if (decl.hasDataConstructor())
							dTypesDecl.add(decl)
						else
							primitiveDtypesDecl.add(decl)
					}
					dtypeMap[decl.qualifiedName] = HeapDecl(decl.type.qualifiedName)
				}
				if(decl is ExceptionDecl) exceptionDecl.add(decl)
				if(decl is InterfaceDecl)  interfaceDecl.add(decl)
			}
		}

	}
	fun libPrefix(type: String): String {
		return when {
			type == "<UNKNOWN>" -> throw Exception("Unknown Type")
			dtypeMap.containsKey(type) || type.startsWith("ABS.StdLib") -> type
			else -> "ABS.StdLib.Int"
		}
	}

}

object FunctionRepos{
    val known : MutableMap<String, FunctionDecl> = mutableMapOf()
	val genericFunctions = mutableMapOf<String,Triple<DataTypeType, List<Type>, Function>>()

    fun isKnown(str: String) = known.containsKey(str)
    fun get(str: String) = known.getValue(str)
	fun hasContracts() = known.filter { hasContract(it.value) }.any()
	private fun contracts() = known.filter { hasContract(it.value) }
    override fun toString() : String {
	    val contracts = contracts()
	    val direct = known.filter { !hasContract(it.value) }
	    var ret = ""

		if(contracts.isNotEmpty()) {
		    var sigs = ""
		    var defs = ""
		    for (pair in contracts) {

				if(pair.value is ParametricFunctionDecl)
					throw Exception("Parametric functions are not supported, please flatten your model")
			    val name = pair.key.replace(".", "-")
			    val params = pair.value.params
				val paramTypes = params.map{
					it.type
				}

			    val zParams = params.joinToString(" ") {
					if(isConcreteGeneric(it.type)) {
						ADTRepos.addGeneric(it.type as DataTypeType)
						genericTypeSMTName(it.type)
					}
			    	else
					ADTRepos.libPrefix(it.type.qualifiedName)
				}

			    val nextsig =  "\n(declare-fun $name ($zParams) ${
					if(isConcreteGeneric(pair.value.type)) {
						ADTRepos.addGeneric(pair.value.type as DataTypeType)
						genericTypeSMTName(pair.value.type)
					}
					else
						ADTRepos.libPrefix(pair.value.type.qualifiedName)})" //todo: use interface to get SMT declaration
			    sigs += nextsig

			    val callParams = params.joinToString(" ") { it.name }

			    val funpre = extractSpec(pair.value, "Requires", pair.value.type)
			    val funpost = extractSpec(pair.value, "Ensures", pair.value.type)

				val paramsTyped = params.joinToString(" ") { "(${it.name} ${
					if(isConcreteGeneric(it.type)) {
						ADTRepos.addGeneric(it.type as DataTypeType)
						genericTypeSMTName(it.type)
					}
					else
					ADTRepos.libPrefix(it.type.qualifiedName)
				})" }
				if(params.count() > 0) {
					val transpost = funpost.toSMT().replace("result","($name $callParams)")
					val nextDef = "\n(assert (forall ($paramsTyped) (=> ${funpre.toSMT()} $transpost)))"

					if(isGeneric(pair.value.type) && !isConcreteGeneric(pair.value.type)){
						println((pair.value.type as DataTypeType).typeArgs)
						genericFunctions[name] = Triple((pair.value.type as DataTypeType), paramTypes,
							Function("(=> ${funpre.toSMT()} $transpost)", params.map{Function(it.name)} ))
					}
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
					sigs += "\t(${pair.key.replace(".", "-")} (${params.fold("") { acc, nx ->
						"$acc (${nx.name} ${

							if (isConcreteGeneric(nx.type)) {
								ADTRepos.addGeneric(nx.type as DataTypeType)
								genericTypeSMTName(nx.type)
							} else
								ADTRepos.libPrefix(nx.type.qualifiedName)
						})"
					}
					})  ${

						if(isConcreteGeneric(def.type)) {
							ADTRepos.addGeneric(def.type as DataTypeType)
							genericTypeSMTName(def.type)
						}
						else
							ADTRepos.libPrefix(def.type.qualifiedName)})\n"
					defs += "\t${exprToTerm(translateExpression(def, def.type, emptyMap())).toSMT()}\n"
			    }
				ret += "\n(define-funs-rec(\n$sigs)(\n$defs))"
		    }
	    return ret
    }

	private fun hasContract(fDecl: FunctionDecl) : Boolean {
		return fDecl.annotationList.any { it.type.toString().endsWith(".Spec") }
	}


	fun init(model: Model) {
		known.clear()
		genericFunctions.clear()
		ADTRepos.clearConcreteGenerics()
		for (mDecl in model.moduleDecls){
			if(mDecl.name.startsWith("ABS.")) continue
			for (decl in mDecl.decls){
				if(decl is FunctionDecl){
					initFunctionDef(decl)
				}
			}
		}
	}

	private fun initFunctionDef(fDecl: FunctionDecl) {
		if(fDecl.functionDef is ExpFunctionDef){
			known[fDecl.qualifiedName] = fDecl
		} else {
			System.err.println("builtin types not supported")
			exitProcess(-1)
		}
	}
	fun extractAll(usedType: KClass<out DeductType>) : List<Pair<String,SymbolicNode>> {
		return known.filter { hasContract(it.value) }.map { Pair(it.key,it.value.extractFunctionNode(usedType)) }
	}

	fun genericFunctionsName(function : Function) :String{
		val genericType = genericFunctions[function.name]!!.first
		val genericParams = genericFunctions[function.name]!!.second
		val concreteParams = function.params.map { param -> getReturnType(param) }

		val mapGenericConcrete = genericParams.zip(concreteParams).filter { pair -> pair.first != pair.second }.toMap()
		val concreteTypes = genericType.typeArgs.map { gT :Type -> if(gT in mapGenericConcrete) mapGenericConcrete[gT] else gT }
		val additionalName = concreteTypes.joinToString("_") { cT -> genericTypeSMTName(cT!!) }
		return "${function.name}_$additionalName"
	}
}

data class Repository(val model : Model?,
					  val classReqs : MutableMap<String,Pair<Formula, ClassDecl>> = mutableMapOf(),
					  val methodReqs : MutableMap<String,Pair<Formula, MethodSig>> = mutableMapOf(),
					  val methodEnss : MutableMap<String,Pair<Formula, MethodSig>> = mutableMapOf(),
					  val syncMethodReqs : MutableMap<String,Pair<Formula, MethodSig>> = mutableMapOf(),
					  val syncMethodEnss : MutableMap<String,Pair<Formula, MethodSig>> = mutableMapOf(),
					  val classFrames : MutableMap<String, MutableMap<Location, AELocSet>> = mutableMapOf()){

    fun populateClassReqs(model: Model) {
        for(moduleDecl in model.moduleDecls) {
            if(moduleDecl.name.startsWith("ABS.")) continue
            for (decl in moduleDecl.decls) {
                if (decl is ClassDecl) {
                    val spec = extractSpec(decl, "Requires", UnknownType.INSTANCE)
                    classReqs[moduleDecl.name+"."+decl.name] = Pair(spec,decl)
                }
            }
        }
    }
    fun populateMethodReqs(model: Model) {
        for(moduleDecl in model.moduleDecls) {
            if(moduleDecl.name.startsWith("ABS.")) continue
            for (decl in moduleDecl.decls) {
                if (decl is InterfaceDecl) {
                    for (mDecl in decl.allMethodSigs) {
                        val spec = extractSpec(mDecl, "Requires", mDecl.type)
                        val spec2 = extractSpec(mDecl, "Ensures", mDecl.type)
                        methodReqs[decl.qualifiedName+"."+mDecl.name] = Pair(spec, mDecl)
                        methodEnss[decl.qualifiedName+"."+mDecl.name] = Pair(spec2, mDecl)
                    }
                }
                if(decl is ClassDecl){
                    for(mImpl in decl.methods){
                        val iUse = getDeclaration(mImpl.methodSig, mImpl.contextDecl as ClassDecl)
                        val syncSpecReq = extractSpec(mImpl, "Requires", mImpl.type)
                        val syncSpecEns = extractSpec(mImpl, "Ensures", mImpl.type)
                        syncMethodReqs[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(syncSpecReq, mImpl.methodSig)
                        syncMethodEnss[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(syncSpecEns, mImpl.methodSig)
                        if(iUse == null){
                            methodReqs[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(True, mImpl.methodSig)
                            methodEnss[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(True, mImpl.methodSig)
                        } else {
                            val spec = extractSpec(iUse.allMethodSigs.first { it.matches(mImpl.methodSig) }, "Requires",
								iUse.allMethodSigs.first { it.matches(mImpl.methodSig) }.type
							)
                            methodReqs[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(spec, mImpl.methodSig)
                            val spec2 = extractSpec(iUse.allMethodSigs.first { it.matches(mImpl.methodSig) }, "Ensures",
								iUse.allMethodSigs.first { it.matches(mImpl.methodSig) }.type
							)
                            methodEnss[decl.qualifiedName+"."+mImpl.methodSig.name] = Pair(spec2, mImpl.methodSig)
                        }
                    }
                }
            }
        }
    }

	fun populateAbstractReqs(model: Model) {
		val betterMainSpec = extractMainTotalSpec(model.mainBlock as MainBlock)
		classFrames["main"] = betterMainSpec

		for(moduleDecl in model.moduleDecls) {
			if(moduleDecl.name.startsWith("ABS.")) continue
			for (decl in moduleDecl.decls) {
				if (decl is ClassDecl) {
					val spec = extractGlobalSpec(decl)
					classFrames["${moduleDecl.name}.${decl.name}"] = spec.first
				}
			}
		}
	}
}