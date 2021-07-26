package org.tud.cgcrawling.download

import akka.http.scaladsl.model.StatusCode

class HttpException(val code: StatusCode) extends Throwable {

  override def getMessage: String = s"Got an unexpected HTTP response, code $code."

}