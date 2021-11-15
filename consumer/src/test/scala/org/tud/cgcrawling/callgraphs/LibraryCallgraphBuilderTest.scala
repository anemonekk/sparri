package org.tud.cgcrawling.callgraphs

import akka.actor.ActorSystem
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.must
import org.tud.cgcrawling.Configuration
import org.tud.cgcrawling.discovery.maven.MavenIdentifier
import org.tud.cgcrawling.model.LibraryCallGraphEvolution

import scala.util.{Failure, Try}

class LibraryCallgraphBuilderTest extends AnyFlatSpec with must.Matchers {

  private val config = new Configuration
  private val identifier1: MavenIdentifier =
    MavenIdentifier(config.mavenRepoBase.toString, "love.forte.simple-robot", "api", "2.3.0")
  private val identifier2: MavenIdentifier =
    MavenIdentifier(config.mavenRepoBase.toString, "com.librato.metrics", "metrics-librato", "5.1.4")

  "The library callgraph builder" must "download 3rd party dependencies for whole-program analysis" in {
    val system = ActorSystem("test-lib-cg-builder")

    Try{
      val builder = new LibraryCallgraphBuilder(identifier2.groupId, identifier2.artifactId, config)(system)

      val evolution = new LibraryCallGraphEvolution(identifier2.groupId, identifier2.artifactId)
      builder.processIdentifier(identifier2, evolution)

      println(s"Got a total of ${evolution.numberOfDependencyEvolutions()} dependencies, ${evolution.releases().size} releases with ${evolution.numberOfMethodEvolutions()} methods and ${evolution.numberOfInvocationEvolutions()} invocations")
      assert(evolution.releases().nonEmpty)

      println("External:")
      evolution.methodEvolutions().filter(mEvo => mEvo.identifier.isExternal).foreach(mEvo => println(mEvo.identifier.fullSignature))

      builder.shutdown()
    } match {
      case Failure(ex) =>
        system.terminate()
        throw ex
      case _ =>
    }
  }
}
