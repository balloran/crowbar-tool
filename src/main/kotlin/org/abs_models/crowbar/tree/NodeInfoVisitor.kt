package org.abs_models.crowbar.tree

interface NodeInfoVisitor<ReturnType> {
    fun visit(info: InfoAwaitUse): ReturnType
    fun visit(info: InfoBranch): ReturnType
    fun visit(info: InfoCallAssign): ReturnType
    fun visit(info: InfoClassPrecondition): ReturnType
    fun visit(info: InfoGetAssign): ReturnType
    fun visit(info: InfoIfElse): ReturnType
    fun visit(info: InfoIfThen): ReturnType
    fun visit(info: InfoInvariant): ReturnType
    fun visit(info: InfoLocAssign): ReturnType
    fun visit(info: InfoLoopInitial): ReturnType
    fun visit(info: InfoLoopPreserves): ReturnType
    fun visit(info: InfoLoopUse): ReturnType
    fun visit(info: InfoMethodPrecondition): ReturnType
    fun visit(info: InfoNullCheck): ReturnType
    fun visit(info: InfoObjAlloc): ReturnType
    fun visit(info: InfoReturn): ReturnType
    fun visit(info: InfoScopeClose): ReturnType
    fun visit(info: InfoSkip): ReturnType
    fun visit(info: InfoSkipEnd): ReturnType
    fun visit(info: InfoSyncCallAssign): ReturnType
    fun visit(info: NoInfo): ReturnType
}