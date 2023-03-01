package de.tudo.sse.spareuse.execution.analyses.impl

import de.tudo.sse.spareuse.core.formats
import de.tudo.sse.spareuse.core.formats.{AnalysisResultFormat, ListResultFormat, NamedPropertyFormat, ObjectResultFormat}
import de.tudo.sse.spareuse.core.maven.MavenIdentifier
import de.tudo.sse.spareuse.core.model.entities.JavaEntities.JavaProgram
import de.tudo.sse.spareuse.core.model.{AnalysisData, SoftwareEntityKind}
import de.tudo.sse.spareuse.core.model.entities.SoftwareEntityData
import de.tudo.sse.spareuse.core.opal.OPALProjectHelper
import de.tudo.sse.spareuse.core.utils.http.HttpDownloadException
import de.tudo.sse.spareuse.execution.analyses.{AnalysisImplementation, Result}
import de.tudo.sse.spareuse.execution.analyses.impl.MvnPartialCallgraphAnalysisImpl.{InternalCallSite, InternalMethod, parseConfig, validCallgraphAlgorithms}
import org.opalj.br.instructions.Instruction
import org.opalj.br.{DeclaredMethod, Method}
import org.opalj.tac.cg.{CHACallGraphKey, CTACallGraphKey, RTACallGraphKey, XTACallGraphKey}

import java.util.concurrent.atomic.AtomicInteger
import scala.util.{Failure, Success, Try}

class MvnPartialCallgraphAnalysisImpl extends AnalysisImplementation {

  private val resultFormat: AnalysisResultFormat = ListResultFormat(
    ObjectResultFormat(Set(
      NamedPropertyFormat("mId", formats.NumberFormat, "The unique id assigned to this method"),
      NamedPropertyFormat("mFqn", formats.StringFormat, "The fully qualified name of this method"),
      NamedPropertyFormat("css", ListResultFormat(ObjectResultFormat(Set(
        NamedPropertyFormat("csPc", formats.NumberFormat, "PC of this callsite inside the enclosing method body"),
        NamedPropertyFormat("targets", ListResultFormat(formats.NumberFormat), "List of method ids that have been resolved as targets for this callsite"),
        NamedPropertyFormat("incomplete", formats.NumberFormat, "Indicates whether the resolution of this callsite was incomplete"),
        NamedPropertyFormat("instr", formats.StringFormat, "String representation of the callsite instruction")
      )), "List of callsites for this method"))
    ))
  , "List of Method definitions with callsite information")

  override val analysisData: AnalysisData = AnalysisData.systemAnalysis("mvn-partial-callgraphs", "1.0.0", "TBD", "OPAL", Set("java", "scala"),
    resultFormat, SoftwareEntityKind.Program)


  override val inputBatchProcessing: Boolean = true

  override def executionPossible(inputs: Seq[SoftwareEntityData], rawConfig: String): Boolean = {

    if(rawConfig.trim.isBlank) return true

    val parts = rawConfig.trim.split(" ")

    for(i <- Range(0, parts.length)){
      if(parts(i).toLowerCase.equals("--algorithm")){
        if( i >= parts.length - 1 || !validCallgraphAlgorithms.exists( algo => algo.toLowerCase.equals(parts(i + 1)))) return false
      } else if(!parts(i).toLowerCase.equals("--use-jre") && !parts(i).equals("--application-mode")) return false
    }

    inputs.forall( sed => sed.isInstanceOf[JavaProgram])
  }

  override def executeAnalysis(inputs: Seq[SoftwareEntityData], rawConfig: String): Try[Set[Result]] = Try {

    val opalHelper = new OPALProjectHelper(loadJreClassImplementation = false)
    val config = parseConfig(rawConfig)

    val opalCgKey = config.algorithm match {
      case "cha" => CHACallGraphKey
      case "rta" => RTACallGraphKey
      case "xta" => XTACallGraphKey
      case "cta" => CTACallGraphKey
      case a@_ => {
        log.warn(s"Invalid CG key after validation: $a")
        XTACallGraphKey
      }
    }


    inputs.map( sed => sed.asInstanceOf[JavaProgram] ).flatMap { program =>
      getFileFor(program) match {
        case Success(inputStream) =>
          val jarUrl = MavenIdentifier.fromGAV(program.name).map(_.toJarLocation.toURL).get
          val classes = opalHelper.readClassesFromJarStream(inputStream, jarUrl, loadImplementation = true).get
          val project = opalHelper.buildOPALProject(classes, List.empty, config.includeJre, setLibraryMode = !config.applicationMode)


          val cg = project.get(opalCgKey)
          val methodIdCnt = new AtomicInteger(0)


          // Build Internal representations without callsites (to assign ids)
          def toMethodObj(definedMethod: Method): InternalMethod = {
            new InternalMethod(methodIdCnt.getAndIncrement(), definedMethod.toJava, List.empty)
          }

          val methodObjLookup: Map[DeclaredMethod, Seq[InternalMethod]] = cg
            .reachableMethods()
            .filter{ declMethod => // Filter out non-project (i.e. JRE) methods
              project.isProjectType(declMethod.declaringClassType)
            }
            .map { declMethod =>
              if(declMethod.hasMultipleDefinedMethods){
                (declMethod, declMethod
                  .asMultipleDefinedMethods
                  .definedMethods
                  .map(toMethodObj))
              } else if(declMethod.hasSingleDefinedMethod){
                (declMethod, Seq(toMethodObj(declMethod.asDefinedMethod.definedMethod)))
              } else {
                (declMethod, Seq(new InternalMethod(methodIdCnt.getAndIncrement(), declMethod.toJava, List.empty)))
              }
            }.toMap

          val allMethodDataWithCallSites = cg
            .reachableMethods()
            .filter { declMethod => // Filter out non-project (i.e. JRE) methods
              project.isProjectType(declMethod.declaringClassType)
            }
            .flatMap{ declMethod =>
              val incompleteCsPcs = cg.incompleteCallSitesOf(declMethod).toSet

              val methodBodies = if(declMethod.hasMultipleDefinedMethods) declMethod.asMultipleDefinedMethods.definedMethods.map(_.body)
                else if(declMethod.hasSingleDefinedMethod) Seq(declMethod.asDefinedMethod.definedMethod.body)
                else Seq.empty

              def getCallSiteInstruction(pc: Int): Option[Instruction] = {
                methodBodies
                  .find(_.isDefined)
                  .map{ codeOpt =>
                    codeOpt.get.instructions(pc)
                  }
              }

              val allMethodCallSites = cg
                .calleesOf(declMethod)
                .map{ callSiteInfo =>
                  val pc = callSiteInfo._1
                  new InternalCallSite(
                    pc, // PC of this callsite
                    callSiteInfo._2.flatMap(dm => methodObjLookup.getOrElse(dm, Seq.empty).map(_.mId)).toList, // All ids of confirmed targets of this callsite
                    incompleteCsPcs.contains(pc), // Whether this callsite is incomplete atm
                    getCallSiteInstruction(pc).map(_.toString(pc)).getOrElse("<none>")
                  )
                }
                .toList

              methodObjLookup(declMethod).map(mObj => mObj.withCallSiteInfo(allMethodCallSites))
            }
            .toList

          log.info(s"Done building partial callgraph representation for ${program.name}")

          Some(Result(allMethodDataWithCallSites, Set(program)))

        case Failure(HttpDownloadException(status, _, _)) if status == 404 =>
          log.warn(s"No JAR file available for ${program.identifier}")
          None
        case Failure(ex) =>
          log.error(s"Failed to download JAR file contents for ${program.identifier}", ex)
          throw ex

      }
    }.toSet

  }
}

object MvnPartialCallgraphAnalysisImpl {

  def validCallgraphAlgorithms: Set[String] = Set("cha", "rta", "cta", "xta")

  case class PartialCallgraphAnalysisConfig(algorithm: String, includeJre: Boolean, applicationMode: Boolean)

  def parseConfig(raw: String): PartialCallgraphAnalysisConfig = {
    var algo = "xta"
    var includeJre = false
    var appMode = false

    val parts = raw.trim.split(" ")

    for (i <- Range(0, parts.length)) {
      if (parts(i).toLowerCase.equals("--algorithm")) {
        algo = parts(i + 1)
      } else if (parts(i).toLowerCase.equals("--use-jre") ) {
        includeJre = true
      } else if(parts(i).toLowerCase.equals("--application-mode")){
        appMode = true
      }
    }

    PartialCallgraphAnalysisConfig(algo, includeJre, appMode)
  }

  class InternalMethod(id: Int, fqn: String, callSites: List[InternalCallSite]){

    def withCallSiteInfo(info: List[InternalCallSite]) =
      new InternalMethod(id, fqn, info)

    val mId: Int = id
    val mFqn: String = fqn
    val css: List[InternalCallSite] = callSites
  }

  class InternalCallSite(pc: Int, resolvedTargetIds: List[Int], isIncomplete: Boolean, instruction: String) {

    val csPc: Int = pc
    val targets: List[Int] = resolvedTargetIds
    val incomplete: Int = if(isIncomplete) 1 else 0
    val instr: String = instruction
  }

}
