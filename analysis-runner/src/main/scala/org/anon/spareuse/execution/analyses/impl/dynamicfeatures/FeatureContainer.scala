package org.anon.spareuse.execution.analyses.impl.dynamicfeatures
import org.opalj.tac.Expr

case class FeatureContainer(kind: String, name: String, declaringClass: String, pc: Int, linenumber: Int, caller: String, params: String/*List[Expr[_]]*/, hostClass: String, classFileVersion: String)


