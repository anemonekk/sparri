package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.Code
import org.opalj.br.analyses.Project
import org.opalj.br.instructions.INVOKEVIRTUAL
import org.opalj.tac.cg.CallGraph
import org.slf4j.{Logger, LoggerFactory}

class Native {

  var result: Set[FeatureContainer] = Set.empty

  protected final val log: Logger = LoggerFactory.getLogger(getClass)

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    for (rm <- cg.reachableMethods()) {

      for (caller <- cg.callersOf(rm.method)) {


        log.info("caller is " + caller)
        if(caller._1.isVirtualOrHasSingleDefinedMethod /*|| caller._1.hasMultipleDefinedMethods*/){

          log.info("caller 2 is " + caller)
          val pc = caller._2

          if(caller._1.definedMethod.body.nonEmpty){
            val bodyS = caller._1.definedMethod.body.get
            if(bodyS.lineNumber(pc).nonEmpty){
              val linenumber = bodyS.lineNumber(pc).get

              val methodbody = caller._1.definedMethod.body
              for (i <- methodbody.toList) {
                i.instructions.toList.foreach(m => m match {
                  case inv: INVOKEVIRTUAL => {
                    if (inv.asVirtualMethod.isMethod) {
                      if (inv.declaringClass.isObjectType) {
                        val objectType = inv.declaringClass.asObjectType
                        val classFile0 = project.classFile(objectType)
                        if (classFile0.nonEmpty) {
                          val localMethod2 = classFile0.get.findMethod(rm.method.name, rm.method.descriptor)
                          if (localMethod2.exists {
                            me =>
                              me.isNative
                          }) {
                            result += FeatureContainer("Native", rm.method.name, rm.method.declaringClassType.fqn,
                              pc, linenumber, caller._1.name, "", "", classFileVersion)
                          }
                        }
                      }
                    }
                  }
                  case _ =>
                })
              }
            }
          }



        }

      }
    }
    result
  }
}
