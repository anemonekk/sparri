package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.analyses.Project
import org.opalj.tac.cg.CallGraph

import scala.annotation.switch

class DynamicProxy {

  val DynProxType = "java/lang/reflect/Proxy"
  val DPNewProxyInstance = "newProxyInstance"

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      (rm.method.declaringClassType.fqn: @switch) match {

        case DynProxType =>

          rm.method.name match {
            case DPNewProxyInstance =>

              for (caller <- cg.callersOf(rm.method)) {

                val pc = caller._2
                val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
                result += FeatureContainer("DP", rm.method.name, rm.method.declaringClassType.fqn,
                  pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
              }

            case _ =>
          }
        case _ =>
      }
    }
    result
  }

}