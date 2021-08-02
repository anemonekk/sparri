package org.tud.cgcrawling.graphgeneration

import akka.actor.ActorSystem
import org.opalj.br.analyses.Project
import org.opalj.tac.cg.{CallGraph, RTACallGraphKey}
import org.slf4j.{Logger, LoggerFactory}
import org.tud.cgcrawling.discovery.maven.MavenIdentifier
import org.tud.cgcrawling.download.MavenDownloadResult
import org.tud.cgcrawling.Configuration

import java.net.URL
import java.util.jar.JarInputStream
import scala.util.{Failure, Success, Try}

class CallGraphBuilder(val config: Configuration, val system: ActorSystem) extends ClassStreamReader {

  private val log: Logger = LoggerFactory.getLogger(this.getClass)

  def buildCallgraph(jarFile: MavenDownloadResult): CallGraphBuilderResult = {
    Try(reifyProject(jarFile, true)) match {
      case Success(project) =>
        log.info(s"Successfully initialized OPAL project for ${jarFile.identifier.toString}")

        val callGraphAlgorithmKey = if(project.codeSize > config.codeSizeCgCutoffBytes){
          log.warn(s"Falling back to RTA because of JAR code size <${project.codeSize}> exceeding limit of <${config.codeSizeCgCutoffBytes}>")
          RTACallGraphKey
        } else {
          config.CallGraphAlgorithm
        }

        Try(project.get(callGraphAlgorithmKey)) match {
          case Success(callgraph) =>
            log.info(s"Successfully generated Callgraph for ${jarFile.identifier.toString}")
            CallGraphBuilderResult(jarFile.identifier, success = true, Some(callgraph), Some(project))
          case Failure(ex) =>
            log.error(s"Failed to generate Callgraph for ${jarFile.identifier.toString}", ex)
            CallGraphBuilderResult(jarFile.identifier, success = false, None, None)
        }
      case Failure(ex) =>
        log.error(s"Error while analyzing JAR for artifact ${jarFile.identifier.toString}", ex)
        CallGraphBuilderResult(jarFile.identifier, success = false, None, None)
    }
  }

  private def reifyProject(m: MavenDownloadResult, loadAsLibraryProject: Boolean): Project[URL] = {
    val jarIs = new JarInputStream(m.jarFile.get.is)

    val project = createProject(m.identifier.toJarLocation.toURL,
      jarIs, loadAsLibraryProject)

    Try{
      jarIs.close()
      m.jarFile.get.is.close()
    } match {
      case Failure(ex) => log.error("Failed to close input streams", ex)
      case _ =>
    }

    project
  }

}

case class CallGraphBuilderResult(identifier: MavenIdentifier,
                                  success: Boolean,
                                  callgraph: Option[CallGraph],
                                  project: Option[Project[URL]])