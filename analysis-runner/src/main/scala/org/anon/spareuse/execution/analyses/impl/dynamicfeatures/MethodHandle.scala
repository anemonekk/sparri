package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.ObjectType
import org.opalj.br.analyses.Project
import org.opalj.tac.cg.CallGraph

import scala.annotation.switch

class MethodHandle {

  val LookupType = ObjectType.MethodHandles$Lookup
  val MethodHandleType = ObjectType.MethodHandle
  val LUFindStatic = "findStatic" // Lookup
  val MHInvokeExact = "invokeExact" // MethodHandle
  val LUFindVirtual = "findVirtual" // Lookup
  val LUFindConstructor = "findConstructor"
  val LUFindStaticGetter = "findStaticGetter"
  val LUFindGetter = "findGetter"
  val LUFindSpecial = "findSpecial"
  val MHInvoke = "invoke" // MethodHandle
  val MHInvokeArguments = "invokeWithArguments" // MethodHandle

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph, publishedAt: String): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      (rm.method.declaringClassType.fqn: @switch) match {

        case MethodHandleType.fqn | LookupType.fqn => rm.method.name match {
          case (LUFindStatic | MHInvokeExact | LUFindVirtual | LUFindConstructor | LUFindStaticGetter |
                LUFindGetter | LUFindSpecial | MHInvoke | MHInvokeArguments) =>

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("MH", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size, publishedAt)
            }

          case _ =>
        }
        case _ =>
      }
    }
    result
  }
}
