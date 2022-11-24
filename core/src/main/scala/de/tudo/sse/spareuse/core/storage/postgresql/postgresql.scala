package de.tudo.sse.spareuse.core.storage

import de.tudo.sse.spareuse.core.model.{AnalysisData, AnalysisResultData, AnalysisRunData, SoftwareEntityKind}
import de.tudo.sse.spareuse.core.model.entities.JavaEntities.JavaProgram
import de.tudo.sse.spareuse.core.model.entities.SoftwareEntityData
import slick.lifted.{ForeignKeyQuery, ProvenShape, Tag}
import slick.jdbc.PostgresProfile.api._


package object postgresql {

  case class SoftwareEntityRepr(id: Long, name: String, fqn: String, language: String, kindId: Int,
                                repository: String, parentId: Option[Long], hexHash: Option[String])

  class SoftwareEntities(tag: Tag) extends Table[SoftwareEntityRepr](tag, "entities") {

    def id: Rep[Long] = column[Long]("ID", O.PrimaryKey, O.AutoInc)

    def name: Rep[String] = column[String]("NAME")

    def qualifier: Rep[String] = column[String]("FQ", O.Unique)

    def language: Rep[String] = column[String]("LANG")

    def kind: Rep[Int] = column[Int]("KIND")

    def repository: Rep[String] = column[String]("REPO")

    def parentID: Rep[Option[Long]] = column[Option[Long]]("PARENT_ID")

    def hash: Rep[Option[String]] = column[Option[String]]("HASH")

    override def * : ProvenShape[SoftwareEntityRepr] =
      (id, name, qualifier, language, kind, repository, parentID, hash)<> ((SoftwareEntityRepr.apply _).tupled, SoftwareEntityRepr.unapply)

    def parent: ForeignKeyQuery[SoftwareEntities, SoftwareEntityRepr] =
      foreignKey("PARENT_FK", parentID, TableQuery[SoftwareEntities])(_.id.?)
  }


  case class SoftwareAnalysisRepr(id: Long, name: String, version: String, description: String, builtOn: String,
                                  registeredBy: String, inputLanguages: String, revoked: Boolean, inputKind: Int){
    def toAnalysisData(executions: Set[AnalysisRunData] = Set.empty): AnalysisData = {
      //TODO: Formats
      AnalysisData(name, version, description, builtOn, registeredBy, inputLanguages.split(",").toSet, revoked,
        null, SoftwareEntityKind.fromId(inputKind), executions)
    }
  }

  def toAnalysisRepr(data: AnalysisData): SoftwareAnalysisRepr = {
    SoftwareAnalysisRepr(-1, data.name, data.version, data.description, data.builtOn, data.registeredBy,
      data.inputLanguages.mkString(","), data.isRevoked, data.inputKind.id)
  }

  class SoftwareAnalyses(tag: Tag) extends Table[SoftwareAnalysisRepr](tag, "analyses") {

    def id: Rep[Long] = column[Long]("ID", O.PrimaryKey, O.AutoInc)

    def name: Rep[String] = column[String]("NAME")

    def version: Rep[String] = column[String]("VERSION")

    def description: Rep[String] = column[String]("DESCRIPTION")

    def builtOn: Rep[String] = column[String]("BUILT_ON")

    def registeredBy: Rep[String] = column[String]("REGISTERED_BY")

    def inputLanguages: Rep[String] = column[String]("LANGUAGES")

    def isRevoked: Rep[Boolean] = column[Boolean]("REVOKED")

    //TODO: Reference to result format

    def inputKind: Rep[Int] = column[Int]("INPUT_KIND")

    override def * : ProvenShape[SoftwareAnalysisRepr] =
      (id, name, version, description, builtOn, registeredBy, inputLanguages, isRevoked, inputKind)<> ((SoftwareAnalysisRepr.apply _).tupled, SoftwareAnalysisRepr.unapply)
  }

  case class SoftwareAnalysisRunRepr(id: Long, uid:String, config: String, isRevoked: Boolean, parentId: Long){

    def toAnalysisRunData(analysisName: String, analysisVersion: String, inputs: Set[SoftwareEntityData] = Set.empty,
                          results: Set[AnalysisResultData] = Set.empty): AnalysisRunData = {
      //TODO: Timestamp, logs, results if requested
      AnalysisRunData(uid, null, Array.empty, config, isRevoked, inputs, results, analysisName, analysisVersion)
    }

  }

  class SoftwareAnalysisRuns(tag: Tag) extends Table[SoftwareAnalysisRunRepr](tag, "analysisruns"){

    def id: Rep[Long] = column[Long]("ID", O.PrimaryKey, O.AutoInc)

    //TODO: Timestamp
    //TODO: Logs

    def uid: Rep[String] = column[String]("UID", O.Unique)

    def configuration: Rep[String] = column[String]("CONFIGURATION")

    def isRevoked: Rep[Boolean] = column[Boolean]("REVOKED")

    def parentID: Rep[Long] = column[Long]("ANALYSIS_ID")


    override def * : ProvenShape[SoftwareAnalysisRunRepr] =
      (id, uid, configuration, isRevoked, parentID) <> ((SoftwareAnalysisRunRepr.apply _).tupled, SoftwareAnalysisRunRepr.unapply)

    def parent: ForeignKeyQuery[SoftwareAnalyses, SoftwareAnalysisRepr] =
      foreignKey("ANALYSIS_FK", parentID, TableQuery[SoftwareAnalyses])(_.id)


  }

  case class AnalysisRunInput(id: Long, analysisRunId: Long, inputEntityId: Long)
  class AnalysisRunInputs(tag: Tag) extends Table[AnalysisRunInput](tag, "anlysisruninputs"){

    def id: Rep[Long] = column[Long]("ID", O.PrimaryKey, O.AutoInc)

    def analysisRunID: Rep[Long] = column[Long]("ANALYSIS_ID")

    def inputEntityID: Rep[Long] = column[Long]("INPUT_ID")

    override def * : ProvenShape[AnalysisRunInput] =
      (id, analysisRunID, inputEntityID) <> ((AnalysisRunInput.apply _).tupled, AnalysisRunInput.unapply)

  }

}
