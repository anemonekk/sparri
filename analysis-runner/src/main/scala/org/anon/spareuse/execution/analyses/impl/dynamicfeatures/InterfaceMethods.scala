package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.analyses.Project
import org.opalj.br.instructions.{INVOKEINTERFACE, INVOKESTATIC, INVOKEVIRTUAL}
import org.opalj.tac.cg.CallGraph

class InterfaceMethods {

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      for (caller <- cg.callersOf(rm.method)) {
        if (!rm.method.name.contains("init")) {

          val pc = caller._2
          if(caller._1.definedMethod.body.get.lineNumber(pc).nonEmpty){
            val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
            val host = caller._1.definedMethod.classFile

            val methodBody = caller._1.definedMethod.body
            for (i <- methodBody.toList) {
              i.instructions.toList.foreach(m => m match {
                case inv: INVOKEVIRTUAL => {
                  if(inv.declaringClass.isObjectType){
                    val subtypes = project.classHierarchy.allSubtypes(inv.declaringClass.asObjectType, true)
                    var isIDM = false
                    subtypes.map {
                      ot =>
                        val target = project.instanceCall(rm.method.declaringClassType, ot, inv.name, inv.methodDescriptor)
                        if (target.hasValue) {
                          val defClass = target.value.asVirtualMethod.classType.asObjectType
                          isIDM = project.classFile(defClass).exists(_.isInterfaceDeclaration)

                          if (project.classFile(defClass).isDefined) {
                            if (target.value.body.isDefined && target.value.isPublic) {
                              if (isIDM) {
                                result += FeatureContainer("Interface Methods default invoke virtual", rm.method.name, rm.method.declaringClassType.fqn,
                                  pc, linenumber, caller._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size)
                              }
                            }
                          }
                        }
                    }
                  }


                }

                case ini: INVOKEINTERFACE => {
                  if(ini.declaringClass.isObjectType){
                    val subtypes = project.classHierarchy.allSubtypes(ini.declaringClass.asObjectType, false)
                    var isIDM = false
                    subtypes.map { ot =>
                      val target = project.instanceCall(rm.method.declaringClassType, ot, ini.name, ini.methodDescriptor)
                      if (target.hasValue) {
                        val defClass = target.value.asVirtualMethod.classType.asObjectType
                        isIDM = project.classFile(defClass).exists(_.isInterfaceDeclaration)

                        if (project.classFile(defClass).isDefined) {
                          if (target.value.body.isDefined && target.value.isPublic) {
                            if(isIDM){
                              result += FeatureContainer("Interface Methods default invoke interface", rm.method.name, rm.method.declaringClassType.fqn,
                                pc, linenumber, caller._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size)
                            }
                          }
                        }
                      }
                    }
                  }
                }
                case ins: INVOKESTATIC => {
                  if (ins.isInterface) {
                    result += FeatureContainer("Interface Methods static invoke static", rm.method.name, rm.method.declaringClassType.fqn,
                      pc, linenumber, caller._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size)
                  }
                }
                case _ =>
              })
            }
          }

        }
      }
    }
    result
  }
}
