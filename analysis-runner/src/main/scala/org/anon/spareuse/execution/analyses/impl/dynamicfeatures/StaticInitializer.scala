package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.ObjectType
import org.opalj.br.analyses.Project
import org.opalj.tac.DUVar
import org.opalj.tac.cg.CallGraph
import org.opalj.value.ValueInformation

import scala.annotation.switch

class StaticInitializer {

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    for ((cf, source) <- project.projectClassFilesWithSources) {
      if (cf.staticInitializer.isDefined) {
        val staticMethods = cf.methods.map(m => if (m.isStatic && !m.isStaticInitializer) {
          m.name
        })

        val si = cf.staticInitializer.get

        result += FeatureContainer("Static Initializer", si.name, si.descriptor.toString(), 1, 1, "static methods: " + staticMethods, "", si.classFile.fqn, si.classFile.jdkVersion, cg.reachableMethods().size)
      }
    }
    result
  }

}
