package org.tud.cgcrawling.storage

import com.rabbitmq.client.{Channel, Connection, ConnectionFactory, MessageProperties}
import org.slf4j.{Logger, LoggerFactory}
import org.tud.cgcrawling.Configuration

import scala.util.{Failure, Success, Try}

class MessageQueuePublisher(configuration: Configuration) {

  val log: Logger = LoggerFactory.getLogger(this.getClass)

  lazy val connection: Connection = {
    val factory = new ConnectionFactory

    factory.setUsername(configuration.mqUsername)
    factory.setPassword(configuration.mqPassword)
    factory.setVirtualHost("/")
    factory.setHost(configuration.mqHost)
    factory.setPort(configuration.mqPort)

    factory.newConnection("incremental-cg-crawler-producer")
  }

  lazy val channel: Channel = connection.createChannel()

  private val exchangeName: String = "lib-ident-exchange"
  private val routingKey: String = ""

  def initialize(): Unit =  {
    Try{
      channel.exchangeDeclare(exchangeName, "direct", true)
      channel.queueDeclare(configuration.mqQueueName, true, false, false, null)
      channel.queueBind(configuration.mqQueueName, exchangeName, routingKey)
    } match {
      case Success(_) =>
        log.info("Successfully initialized queue")
      case Failure(ex) =>
        log.error("Failed to initialize queue", ex)
    }

  }

  def publishLibraryIdentifier(identifier: String): Unit = {
    channel.basicPublish(exchangeName,
      routingKey,
      MessageProperties.PERSISTENT_TEXT_PLAIN,
      identifier.getBytes)
  }

  def shutdown(): Unit = {
    connection.close()
    log.info("Shutdown complete")
  }
}
