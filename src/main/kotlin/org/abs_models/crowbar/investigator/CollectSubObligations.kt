package org.abs_models.crowbar.investigator

import org.abs_models.crowbar.data.And
import org.abs_models.crowbar.data.Formula

fun collectSubObligations(form: Formula): Set<Formula> {
    val worklist = mutableListOf<Formula>(form)
    val collected = mutableSetOf<Formula>()

    while (worklist.isNotEmpty()) {
        val item = worklist.removeAt(0)
        if (item is And) {
            worklist.add(item.left)
            worklist.add(item.right)
        } else
            collected.add(item)
    }

    return collected
}
