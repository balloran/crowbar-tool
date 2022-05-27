package org.abs_models.crowbar.types

import org.abs_models.crowbar.data.DeductType
import org.abs_models.crowbar.main.Repository
import org.abs_models.crowbar.tree.SymbolicNode
import org.abs_models.frontend.ast.ClassDecl
import org.abs_models.frontend.ast.FunctionDecl
import org.abs_models.frontend.ast.Model

interface RelationType : DeductType{
    companion object : RelationType {
        override fun extractMethodNode(classDecl: ClassDecl, name: String, repos: Repository): SymbolicNode {
            TODO("Not yet implemented")
        }

        override fun extractInitialNode(classDecl: ClassDecl): SymbolicNode {
            TODO("Not yet implemented")
        }

        override fun extractMainNode(model: Model): SymbolicNode {
            TODO("Not yet implemented")
        }

        override fun extractFunctionNode(fDecl: FunctionDecl): SymbolicNode {
            TODO("Not yet implemented")
        }
    }
}