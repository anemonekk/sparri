package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.ObjectType
import org.opalj.br.analyses.Project
import org.opalj.tac.cg.CallGraph

import scala.annotation.switch

class Unsafe {

  val UnsafeType = ObjectType("sun/misc/Unsafe")

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      (rm.method.declaringClassType.fqn: @switch) match {
        case UnsafeType.fqn =>

          if(rm.method.name.contains("compareAndSwap")){

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe CAS", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
           }

          if ((rm.method.name.contains("put") && !(rm.method.name.contains("Ordered")) &&
            !(rm.method.name.contains("Volatile"))) ||
            (rm.method.name.contains("get")) && !(rm.method.name.contains("Volatile")) &&
              !(rm.method.name.contains("LoadAverage")) && !(rm.method.name.contains("And"))) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe Heap", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }

          if (rm.method.name.contains("getAnd")) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe FetchAndAdd", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }

          if (rm.method.name.contains("putOrdered")) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe OrderedPut", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }

          if (rm.method.name.contains("Volatile")) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe Volatile", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }

          if (rm.method.name.equals("allocateInstance")) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe Alloc", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }

          if (rm.method.name.contains("Fence")) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe Fence", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }

          if (rm.method.name.contains("Class") || rm.method.name.equals("shouldBeInitialized")) {

            for (caller <- cg.callersOf(rm.method)) {

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              result += FeatureContainer("Unsafe Class", rm.method.name, rm.method.declaringClassType.fqn,
                pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
            }
          }
        case _ =>
      }
    }
    result
  }
}
