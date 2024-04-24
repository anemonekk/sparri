package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.analyses.Project
import org.opalj.tac.cg.CallGraph

class Native {

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph, publishedAt: String): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      for (caller <- cg.callersOf(rm.method)) {

        if(caller._1.isVirtualOrHasSingleDefinedMethod /*|| caller._1.hasMultipleDefinedMethods*/){

          val pc = caller._2

          if(caller._1.definedMethod.body.nonEmpty){
            val bodyS = caller._1.definedMethod.body.get
            if(bodyS.lineNumber(pc).nonEmpty){
              val linenumber = bodyS.lineNumber(pc).get

              if(rm.method.hasSingleDefinedMethod){
                if(rm.method.definedMethod.isNative){
                  result += FeatureContainer("Native", rm.method.name, rm.method.declaringClassType.fqn,
                    pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size, publishedAt)
                }
              }
            }
          }
        }
      }
    }
    result
  }
}
