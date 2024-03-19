package org.anon.spareuse.execution.analyses.impl

import org.anon.spareuse.core.formats
import org.anon.spareuse.core.formats.{AnalysisResultFormat, ListResultFormat, NamedPropertyFormat, ObjectResultFormat}
import org.anon.spareuse.core.maven.MavenIdentifier
import org.anon.spareuse.core.model.{AnalysisData, SoftwareEntityKind}
import org.anon.spareuse.core.model.entities.JavaEntities.JavaProgram
import org.anon.spareuse.core.model.entities.SoftwareEntityData
import org.anon.spareuse.core.opal.OPALProjectHelper
import org.anon.spareuse.execution.analyses.impl.dynamicfeatures.{Classloading, DynamicProxy, MethodHandle, Unsafe}
import org.anon.spareuse.execution.analyses.{AnalysisImplementation, AnalysisImplementationDescriptor, AnalysisResult, FreshResult}
import org.opalj.tac.cg.RTACallGraphKey

import java.io.InputStream
import scala.util.{Failure, Success, Try}

class DynamicFeatureExtractor extends AnalysisImplementation{

  override def executionPossible(inputs: Seq[SoftwareEntityData], rawConfig: String): Boolean = true

  override val descriptor: AnalysisImplementationDescriptor = DynamicFeatureExtractor

  override def executeAnalysis(inputs: Seq[SoftwareEntityData], configRaw: String): Try[Set[AnalysisResult]] = Try {

    val opalHelper = new OPALProjectHelper(loadJreClassImplementation = false)

    inputs.map(sed => sed.asInstanceOf[JavaProgram]).flatMap { program =>
      getFileFor(program) match {
        case Success(inputStream: InputStream) => {
          val jarUrl = MavenIdentifier.fromGAV(program.name).map(_.toJarLocation.toURL).get
          val classes = opalHelper.readClassesFromJarStream(inputStream, jarUrl, loadImplementation = true).get
          val project = opalHelper.buildOPALProject(classes, List.empty, /*config.includeJre,*/ setLibraryMode = /*!config.applicationMode*/ true)

          val cg = project.get(RTACallGraphKey)

          val clBuilder: Classloading = new Classloading
          //val reflBuilder: ReflectionFeature = new ReflectionFeature
          val dynProxBuilder: DynamicProxy = new DynamicProxy
          val methodhandleBuilder: MethodHandle = new MethodHandle
          val unsafeBuilder: Unsafe = new Unsafe
          //val interfaceMethodsBuiler: InterfaceMethods = new InterfaceMethods
          //val nativeBuilder: Native = new Native

          //val reflFeatures = reflBuilder.apply(project, cg)
          val classloadingFeatures = clBuilder.apply(project, cg)
          val dynamicProxyFeatures = dynProxBuilder.apply(project, cg)
          //val interfaceMethodsFeatures = interfaceMethodsBuiler.apply(project, cg)
          val methodhandleFeatures = methodhandleBuilder.apply(project, cg)
          //val nativeFeatures = nativeBuilder.apply(project, cg)
          val unsafeFeatures = unsafeBuilder.apply(project, cg)

          val mergeFeatures = (/*reflFeatures ++*/ classloadingFeatures ++ dynamicProxyFeatures
            /*++ interfaceMethodsFeatures*/ ++ methodhandleFeatures /*++ nativeFeatures*/
            ++ unsafeFeatures).toList

          Some(FreshResult(mergeFeatures, Set(program)))
        }
        case Failure(ex) =>
          log.error("feature identification failed", ex)
          throw ex
      }

    }.toSet
  }
}

object DynamicFeatureExtractor extends AnalysisImplementationDescriptor {

  private val resultFormat: AnalysisResultFormat = ListResultFormat(
    ObjectResultFormat(
      Set(
        NamedPropertyFormat("kind", formats.StringFormat),
        NamedPropertyFormat("name", formats.StringFormat),
        NamedPropertyFormat("declaringClass", formats.StringFormat),
        NamedPropertyFormat("pc", formats.NumberFormat),
        NamedPropertyFormat("linenumber", formats.NumberFormat),
        NamedPropertyFormat("caller", formats.StringFormat),
        NamedPropertyFormat("params", formats.StringFormat),
        NamedPropertyFormat("hostClass", formats.StringFormat),
        NamedPropertyFormat("classFileVersion", formats.StringFormat)
      )
    )
  )

  override val analysisData: AnalysisData = AnalysisData.systemAnalysis(
    "mvn-dynamic-features",
    "1.0.0",
    "This analysis uses OPAL to ...",
    "OPAL",
    Set("java", "scala"),
    resultFormat,
    SoftwareEntityKind.Program,
    doesBatchProcessing = true,
    isIncremental = false)
}