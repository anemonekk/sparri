package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.{ObjectType}
import org.opalj.br.analyses.Project
import org.opalj.tac.{DUVar}
import org.opalj.tac.cg.CallGraph
import org.opalj.value.{ValueInformation}

import scala.annotation.switch

class Classloading {

  val ClassLoaderType = ObjectType("java/lang/ClassLoader")
  val ClassLoaderNetURLType = ObjectType("java/net/URLClassLoader")
  type V = DUVar[ValueInformation]

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      (rm.method.declaringClassType.fqn: @switch) match {
        // TODO: more subclasses
        case ClassLoaderType.fqn | ClassLoaderNetURLType.fqn =>

          rm.method.name match {
            case "loadClass" =>

              for (caller <- cg.callersOf(rm.method)) {

                val pc = caller._2
                val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
                result += FeatureContainer("CL", rm.method.name, rm.method.declaringClassType.fqn,
                  pc, linenumber, caller._1.name, "", "", classFileVersion)
              }

            case _ =>
          }
        case _ =>
      }
    }
    result
  }
}