package de.tudo.sse.classfilefeatures.webapi.model.requests

import akka.http.scaladsl.marshallers.sprayjson.SprayJsonSupport
import spray.json.{DefaultJsonProtocol, JsonFormat}

trait RequestsJsonSupport extends SprayJsonSupport with DefaultJsonProtocol {

  implicit val enqueueRequestFormat: JsonFormat[EnqueueRequest] = jsonFormat1(EnqueueRequest)

}
