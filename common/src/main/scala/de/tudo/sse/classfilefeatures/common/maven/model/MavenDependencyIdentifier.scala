package de.tudo.sse.classfilefeatures.common.maven.model

case class MavenDependencyIdentifier(identifier: MavenIdentifier, scope: String = "default") {

  override def equals(obj: Any): Boolean = obj match {
    case other: MavenDependencyIdentifier => other.identifier.equals(identifier) && other.scope.equals(scope)
    case _ => false
  }

  override def hashCode(): Int = {
    41 * identifier.hashCode() + 13 * scope.hashCode
  }

}