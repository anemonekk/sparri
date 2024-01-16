package org.anon.spareuse.execution.analyses.impl.cg

import org.anon.spareuse.core.model.entities.JavaEntities.JavaProgram
import org.anon.spareuse.core.model.entities.conversion.OPALJavaConverter
import org.anon.spareuse.core.opal.OPALProjectHelper
import org.anon.spareuse.execution.AnalysisRunnerConfig
import org.anon.spareuse.execution.analyses.{getCallGraphProject, toObjectModel}
import org.opalj.br.MethodDescriptor
import org.opalj.br.analyses.Project
import org.scalatest.funspec.AnyFunSpec

import java.net.URL

class OTF_RTA_BuilderTest extends AnyFunSpec {

  private val objFqn: String = "java/lang/Object"
  private val theOpalHelper: OPALProjectHelper = new OPALProjectHelper(loadJreClassImplementation = false)

  private lazy val jreObjectModel = {
    println("Loading JRE domain model, this might take some time ... ")
    val jreProg = OPALJavaConverter.convertProgram("<NONE>:<THE_JRE>", "<default>", theOpalHelper.jreClasses.map(_._1), loadClassContents = false)
    assert(jreProg.allClasses.exists(_.thisType == objFqn))
    assert(jreProg.allClasses.nonEmpty)
    println(s"Done loading ${jreProg.allClasses.size} JRE classes")
    theOpalHelper.freeOpalResources()
    jreProg
  }

  private val cgOpalProject: Project[URL] = getCallGraphProject
  private def getCgFixtureModel: JavaProgram = toObjectModel(cgOpalProject)
  private def resetModelLoader(): Unit = {
    JreModelLoader.clear()
    JreModelLoader.indexJreData(new AnalysisRunnerConfig("", 3, false, "jre-data"))
  }

  describe("The On-the-Fly RTA CG Builder") {
    it("should correctly stitch the type hierarchy without the JRE present"){
      val input = getCgFixtureModel
      val builder = new OTF_RTA_Builder(Set(input), None)

      cgOpalProject.allClassFiles.map(_.fqn).foreach { fqn =>
        assert(builder.typeLookup.contains(fqn))
      }

      val callTargetImplNode = builder.typeLookup("CallTargetImpl")
      assert(callTargetImplNode.hasParent)
      assert(callTargetImplNode.hasInterfaces)
      assert(callTargetImplNode.getInterfaces.size == 1)

      val theParent = callTargetImplNode.getParent.get
      assert(theParent.thisType == "Calls")
      assert(!theParent.hasParent)
      assert(theParent.superTypeOpt.isDefined && theParent.superTypeOpt.get == objFqn)
      assert(theParent.isIncomplete)
      assert(!theParent.hasInterfaces)

      val theInterface = callTargetImplNode.getInterfaces.head
      assert(theInterface.isInterface)
      assert(!theInterface.hasParent)
      assert(!theInterface.hasInterfaces)
      assert(theInterface.thisType == "CallTarget")

      assert(theInterface.getChildren.contains(callTargetImplNode))
    }

    it("should build a type hierarchy for the JRE itself"){
      val builder = new OTF_RTA_Builder(Set(jreObjectModel), None)

      assert(builder.typeLookup.nonEmpty)

      val objNode = builder.typeLookup(objFqn)
      assert(!objNode.hasParent)
      assert(!objNode.hasInterfaces)
      assert(!objNode.isIncomplete)

      println(s"Object type has ${objNode.getChildren.size} direct children")
    }

    it("should correctly stitch the type hierarchy with the JRE present"){
      resetModelLoader()
      val input = getCgFixtureModel

      val builder = new OTF_RTA_Builder(Set(input), Some(JreModelLoader.defaultJre))

      cgOpalProject.allClassFiles.map(_.fqn).foreach { fqn =>
        assert(builder.typeLookup.contains(fqn))
      }

      val callsNode = builder.typeLookup("Calls")
      assert(callsNode.hasParent)
      assert(callsNode.getParent.get.thisType == objFqn)
      assert(!callsNode.isIncomplete)
    }

    it("should work for static calls in naive mode even on incomplete type hierarchies"){
      val input = getCgFixtureModel
      val builder = new OTF_RTA_Builder(Set(input), None)

      val result = builder.buildNaive()
      assert(result.isSuccess)

      assert(builder.callSiteResolutions.nonEmpty)
      assert(builder.callSiteResolutions.contains("Calls") && builder.callSiteResolutions("Calls").methodResolutions.keys.count(_.methodName == "doStaticCalls") == 1)

      val methodResolutions =  builder.callSiteResolutions("Calls").methodResolutions.values.find(_.methodInfo.methodName == "doStaticCalls").get

      assert(methodResolutions.callSiteResolutions.size == 2)
      assert(methodResolutions.callSiteResolutions.contains(0) && methodResolutions.callSiteResolutions.contains(5))
      val res1 = methodResolutions.callSiteResolutions(0)
      val res2 = methodResolutions.callSiteResolutions(5)

      assert(res1.size == 1)
      assert(res2.size == 1)

      val r1 = res1.head
      val r2 = res2.head

      assert(r1 == r2)
      assert(r1.definingTypeName == "Calls")
      assert(r1.methodName == "doFoo")
      assert(MethodDescriptor(r1.descriptor) == MethodDescriptor.NoArgsAndReturnVoid)
    }

    it("should resolve some virtual calls in naive mode even on incomplete type hierarchies"){
      val input = getCgFixtureModel
      val builder = new OTF_RTA_Builder(Set(input), None)

      val result = builder.buildNaive()
      assert(result.isSuccess)

      assert(builder.callSiteResolutions.nonEmpty)
      assert(builder.callSiteResolutions.contains("Calls") && builder.callSiteResolutions("Calls").methodResolutions.keys.count(_.methodName == "doVirtualCalls") == 1)

      val methodResolutions = builder.callSiteResolutions("Calls").methodResolutions.values.find(_.methodInfo.methodName == "doVirtualCalls").get

      // Expect four INVOKESPECIAL and three INVOKEVIRTUAL (Object.toString cannot be resolved here!)
      assert(methodResolutions.callSiteResolutions.size == 7)

      val expectedCallSitePcs = Set(28, 40, 54)
      assert(expectedCallSitePcs.forall(pc => methodResolutions.callSiteResolutions.contains(pc)))
      assert(!methodResolutions.callSiteResolutions.contains(15)) // Make sure "toString" on "Object" is not resolved without JRE

      val callSite1Targets = methodResolutions.callSiteResolutions(28)
      assert(callSite1Targets.size == 2)
      assert(callSite1Targets.exists(dm => dm.definingTypeName == "Calls" && dm.methodName == "doStaticCalls" &&
        MethodDescriptor(dm.descriptor) == MethodDescriptor.NoArgsAndReturnVoid))
      assert(callSite1Targets.exists(dm => dm.definingTypeName == "CallTargetImpl" && dm.methodName == "doStaticCalls" &&
        MethodDescriptor(dm.descriptor) == MethodDescriptor.NoArgsAndReturnVoid))

      val callSite2Targets = methodResolutions.callSiteResolutions(40)
      assert(callSite2Targets.size == 2)
      assert(callSite2Targets.exists(dm => dm.definingTypeName == "Calls" && dm.methodName == "doStaticCalls" &&
        MethodDescriptor(dm.descriptor) == MethodDescriptor.NoArgsAndReturnVoid))
      assert(callSite2Targets.exists(dm => dm.definingTypeName == "CallTargetImpl" && dm.methodName == "doStaticCalls" &&
        MethodDescriptor(dm.descriptor) == MethodDescriptor.NoArgsAndReturnVoid))

      val callSite3Targets = methodResolutions.callSiteResolutions(54)
      assert(callSite3Targets.size == 1)
      val callSite3 = callSite3Targets.head
      assert(callSite3.definingTypeName == "CallTargetImpl" && callSite3.methodName == "doStaticCalls" &&
        MethodDescriptor(callSite3.descriptor) == MethodDescriptor.NoArgsAndReturnVoid)

    }

    it("should resolve all virtual calls when full JRE summaries are used in naive mode") {
      resetModelLoader()
      val input = getCgFixtureModel
      val builder = new OTF_RTA_Builder(Set(input), Some(JreModelLoader.defaultJre))

      val result = builder.buildNaive()
      assert(result.isSuccess)

      assert(builder.callSiteResolutions.nonEmpty)
      assert(builder.callSiteResolutions.contains("Calls") && builder.callSiteResolutions("Calls").methodResolutions.keys.count(_.methodName == "doVirtualCalls") == 1)

      val methodResolutions = builder.callSiteResolutions("Calls").methodResolutions.values.find(_.methodInfo.methodName == "doVirtualCalls").get

      // Expect four INVOKESPECIAL and four INVOKEVIRTUAL - Object.toString must be resolved here!
      assert(methodResolutions.callSiteResolutions.size == 8)

      assert(methodResolutions.callSiteResolutions.contains(15)) // Make sure "toString" on "Object" is resolved with JRE

      val toStringTargets = methodResolutions.callSiteResolutions(15)

      assert(toStringTargets.nonEmpty)
      val allInstantiatedTypes = JreModelLoader.getDefaultJre.get.allTypesInstantiated ++ input.allClasses.flatMap(c => c.getMethods.flatMap(m => m.getNewStatements.map(_.instantiatedTypeName)))
      assert(toStringTargets.size <= allInstantiatedTypes.size)

      // Check that (of the fixture classes) only the one defining a toString method is invoked
      assert(toStringTargets.forall(dm => dm.methodName == "toString" && MethodDescriptor(dm.descriptor) == MethodDescriptor.JustReturnsString))
      assert(toStringTargets.exists(dm => dm.definingTypeName == "CallTargetImpl"))
      assert(!toStringTargets.exists(dm => dm.definingTypeName == "Calls"))
      assert(!toStringTargets.exists(dm => dm.definingTypeName == "BranchingTaint"))
      assert(!toStringTargets.exists(dm => dm.definingTypeName == "CallTarget"))

      // Assert that all potential targets are instantiated somewhere in the code
      assert(toStringTargets.forall(dm => allInstantiatedTypes.contains(dm.definingTypeName)))

      val allCallSitesCount = builder.callSiteResolutions.values.map(ccsr => ccsr.methodResolutions.values.map(mcsr => mcsr.callSiteResolutions.size).sum).sum
      val allTargetsCount = builder.callSiteResolutions.values.map(ccsr => ccsr.methodResolutions.values.map(mcsr => mcsr.callSiteResolutions.values.map(_.size).sum).sum).sum

      println(s"Resolved $allCallSitesCount callsites to $allTargetsCount methods")
    }

  }

}
