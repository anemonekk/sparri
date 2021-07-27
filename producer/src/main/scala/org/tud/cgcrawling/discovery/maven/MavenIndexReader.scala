package org.tud.cgcrawling.discovery.maven

import akka.NotUsed
import akka.stream.scaladsl.{RestartSource, Source}
import org.apache.maven.index.reader.IndexReader
import org.slf4j.{Logger, LoggerFactory}

import java.net.{URI, URL}
import java.util
import scala.concurrent.duration.DurationInt
import scala.util.{Failure, Success, Try}

class MavenIndexReader(base: URL) {
  val log: Logger = LoggerFactory.getLogger(this.getClass)

  log.info(s"New maven index reader create for $base")
  val ir = new IndexReader(null, new HttpResourceHandler(base.toURI.resolve(".index/")))

  log.info("Index Reader created")
  log.debug(ir.getIndexId)
  log.debug(ir.getPublishedTimestamp.toString)
  log.debug(ir.isIncremental.toString)
  log.debug(ir.getChunkNames.toString)

  lazy val cr = ir.iterator().next().iterator()


  def read(): Option[MavenIdentifier] = {

    def readInternal(kvp: util.Map[String, String]) = {
      val kvpU = Option(kvp.get("u"))

      if(kvpU.isEmpty){
        None
      } else {
        val identifierAttempt = Try(kvpU.get.split("|".toCharArray))

        identifierAttempt match {
          case Success(identifier) => {
            val mavenId = MavenIdentifier(base.toString, identifier(0), identifier(1), identifier(2))

            Some(mavenId)
          }
          case Failure(e) => {
            log.warn(s"While processing index we received the following u-value that we could not split $kvpU. Full kvp is $kvp. Exception was $e.")
            None
          }
        }
      }
    }

    while(cr.hasNext){
      readInternal(cr.next()) match {
        case Some(x) => return Some(x)
        case _ =>
      }
    }

    None
  }

  def close() = {
    ir.close()
  }
}

trait IndexProcessing {

  private val log: Logger = LoggerFactory.getLogger(this.getClass)

  def createSource(base: URI): Source[MavenIdentifier, NotUsed] = {
    log.info("Creating source")

    RestartSource.onFailuresWithBackoff(
      minBackoff = 30.seconds,
      maxBackoff = 90.seconds,
      randomFactor = 0.2, // adds 20% "noise" to vary the intervals slightly
      maxRestarts = 20 // limits the amount of restarts to 20
    ) { () => {
      val ir = Try(new MavenIndexReader(base.toURL))
      ir match {
        case Success(indexReader) => {
          Source.unfoldResource[MavenIdentifier, MavenIndexReader](
            () => indexReader,
            reader => reader.read(),
            reader => reader.close())
        }
        case Failure(e)
        => {
          log.error(s"Could not reach resource. Terminating crawling for $base.")
          throw e
        }
      }
    }
    }
  }

}
