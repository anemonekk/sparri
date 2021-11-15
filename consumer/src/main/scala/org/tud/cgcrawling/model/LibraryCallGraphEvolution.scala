package org.tud.cgcrawling.model

import org.opalj.br.{DeclaredMethod, VirtualDeclaredMethod}
import org.opalj.br.analyses.Project
import org.opalj.tac.cg.CallGraph
import org.slf4j.{Logger, LoggerFactory}
import org.tud.cgcrawling.opal.OPALProjectHelper

import java.net.URL
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class LibraryCallGraphEvolution(val groupId: String, val artifactId: String) {

  private val log: Logger = LoggerFactory.getLogger(this.getClass)

  private val methodEvolutionMap: mutable.Map[MethodIdentifier, MethodEvolution] = new mutable.HashMap()
  private val invocationEvolutionMap: mutable.Map[MethodInvocationIdentifier, MethodInvocationEvolution] =
    new mutable.HashMap()
  private val dependencyEvolutionMap: mutable.Map[DependencyIdentifier, DependencyEvolution] = new mutable.HashMap()


  private val releaseList: mutable.ListBuffer[String] = new ListBuffer[String]

  val libraryName = s"$groupId:$artifactId"

  def releases(): List[String] = releaseList.toList
  def methodEvolutions(): Iterable[MethodEvolution] = methodEvolutionMap.values
  def methodInvocationEvolutions(): Iterable[MethodInvocationEvolution] = invocationEvolutionMap.values
  def dependencyEvolutions(): Iterable[DependencyEvolution] = dependencyEvolutionMap.values

  def numberOfMethodEvolutions(): Int = methodEvolutionMap.size
  def numberOfInvocationEvolutions(): Int = invocationEvolutionMap.size
  def numberOfDependencyEvolutions(): Int = dependencyEvolutionMap.size

  def dependenciesAt(release: String): Iterable[DependencyIdentifier] = {
    if(!releaseList.contains(release))
      throw new RuntimeException(s"Unknown release $release")

    dependencyEvolutions()
      .filter(_.isActiveIn.contains(release))
      .map(_.identifier)
  }

  def methodsAt(release: String): Iterable[MethodIdentifier] = {
    if(!releaseList.contains(release))
      throw new RuntimeException(s"Unknown release $release")

    methodEvolutions()
      .filter(_.isActiveIn.contains(release))
      .map(_.identifier)
  }

  def calleesAt(caller: MethodIdentifier, release: String): Iterable[MethodIdentifier] ={
    if(!releaseList.contains(release))
      throw new RuntimeException(s"Unknown release $release")

    if(!methodEvolutionMap.contains(caller) || !methodEvolutionMap(caller).isActiveIn.contains(release))
      throw new RuntimeException(s"Method $caller was not active in release $release")

    invocationEvolutionMap
      .keys
      .filter(_.calleeIdent.equals(caller))
      .filter(invocationEvolutionMap(_).isActiveIn.contains(release))
      .map(_.calleeIdent)
      .toList
  }

  def applyNewRelease(callgraph: CallGraph,
                      project: Project[URL],
                      dependencies: Set[DependencyIdentifier],
                      release: String): Unit = {

    if(releaseList.contains(release)){
      throw new RuntimeException(s"Release has already been applied to CallGraphEvolution: $release")
    }

    log.info(s"Processing new release $release for $libraryName")
    releaseList.append(release)

    dependencies.foreach(setDependencyActiveInRelease(_, release))

    val projectMethods = callgraph
      .reachableMethods()
      .filter(m => !isExternalMethod(m, project))
      .toSet

    projectMethods
      .foreach { method =>
        val callerIdent = MethodIdentifier.fromOpalMethod(method, false)

        setMethodActiveInRelease(callerIdent, release)

        callgraph
          .calleesOf(method)
          .flatMap(_._2)
          .map(m => MethodIdentifier.fromOpalMethod(m, isExternalMethod(m, project)))
          .toList
          .foreach{ calleeIdent =>
            setMethodActiveInRelease(calleeIdent, release)

            val ident = new MethodInvocationIdentifier(callerIdent, calleeIdent)
            setInvocationActiveInRelease(ident, release)
          }
      }
  }

  private def setDependencyActiveInRelease(identifier: DependencyIdentifier, release: String): Unit = {
    if(!dependencyEvolutionMap.contains(identifier)){
      dependencyEvolutionMap.put(identifier, new DependencyEvolution(identifier))
    }

    dependencyEvolutionMap(identifier).addActiveRelease(release)
  }

  private def setInvocationActiveInRelease(identifier: MethodInvocationIdentifier, release: String): Unit = {
    if(!invocationEvolutionMap.contains(identifier)){
      invocationEvolutionMap.put(identifier, new MethodInvocationEvolution(identifier))
    }

    invocationEvolutionMap(identifier).addActiveRelease(release)
  }

  private def setMethodActiveInRelease(identifier: MethodIdentifier, release: String): Unit = {
    if(!methodEvolutionMap.contains(identifier)){
      methodEvolutionMap.put(identifier, new MethodEvolution(identifier))
    }
    methodEvolutionMap(identifier).addActiveRelease(release)
  }

  private def isExternalMethod(method: DeclaredMethod, project: Project[URL]): Boolean = {
    OPALProjectHelper.isThirdPartyMethod(project, method)
  }
}



