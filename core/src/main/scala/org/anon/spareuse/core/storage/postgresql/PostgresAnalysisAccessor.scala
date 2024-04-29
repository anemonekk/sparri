package org.anon.spareuse.core.storage.postgresql

import org.anon.spareuse.core.formats.{AnalysisResultFormat, AnyValueFormat, BaseValueFormat, EmptyFormat, EntityReferenceFormat, GraphResultFormat, ListResultFormat, MapResultFormat, NamedPropertyFormat, NumberFormat, ObjectResultFormat, StringFormat}
import org.anon.spareuse.core.model.{AnalysisData, AnalysisResultData, AnalysisRunData, RunState}
import org.anon.spareuse.core.model.RunState.RunState
import org.anon.spareuse.core.model.entities.SoftwareEntityData
import slick.dbio.DBIO
import slick.jdbc.PostgresProfile.api._
import spray.json.JsonWriter

import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.UUID
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success, Try}

trait PostgresAnalysisAccessor {
  this: PostgresEntityAccessor with PostgresSparriSupport =>

  implicit val executor: ExecutionContext

  override def registerIfNotPresent(analysis: AnalysisData): Unit = {
    if (!hasAnalysis(analysis.name, analysis.version)) {

      val formatId = storeResultFormat(analysis.resultFormat)

      val insertF = db.run(analysesTable += toAnalysisRepr(analysis, formatId))

      Await.result(insertF, simpleQueryTimeout)
    }
  }

  private def getAnalysisRepr(analysisName: String, analysisVersion: String): SoftwareAnalysisRepr = {
    val queryF = db.run(analysesTable.filter(a => a.name === analysisName && a.version === analysisVersion).take(1).result)

    Await.result(queryF, simpleQueryTimeout).headOption match {
      case Some(result) => result
      case None => throw new IllegalStateException(s"Analysis $analysisName:$analysisVersion no present in db")
    }
  }

  override def getAnalysisData(analysisName: String, analysisVersion: String, includeRuns: Boolean = false): Try[AnalysisData] = Try {

    val repr = getAnalysisRepr(analysisName, analysisVersion)

    val analysisRuns = if (includeRuns) getAnalysisRuns(repr.id, analysisName, analysisVersion, includeResults = false, skip = 0, limit = 500)
    else Set.empty[AnalysisRunData]

    getResultFormat(repr.formatId) match {
      case f: AnalysisResultFormat =>
        repr.toAnalysisData(f, analysisRuns)
      case _ =>
        throw new IllegalStateException("Corrupt format definition: Analysis result format must not be base value")
    }
  }


  override def getAnalyses(includeRuns: Boolean = false, skip: Int = 0, limit: Int = 100): Try[Set[AnalysisData]] = Try {

    val queryF = db.run(analysesTable.sortBy(_.id).drop(skip).take(limit).result)

    Await
      .result(queryF, simpleQueryTimeout)
      .map { analysisRepr =>
        val analysisRuns = if (includeRuns) getAnalysisRuns(analysisRepr.id, analysisRepr.name, analysisRepr.version, includeResults = false, skip = 0, limit = 500)
        else Set.empty[AnalysisRunData]

        getResultFormat(analysisRepr.formatId) match {
          case f: AnalysisResultFormat =>
            analysisRepr.toAnalysisData(f, analysisRuns)
          case _ =>
            throw new IllegalStateException("Corrupt format definition: Analysis result format must not be base value")
        }
      }.toSet
  }

  override def getAnalysesFor(analysisName: String, includeRuns: Boolean = false): Try[Set[AnalysisData]] = Try {
    val queryF = db.run(analysesTable.filter(_.name === analysisName).result)

    Await
      .result(queryF, simpleQueryTimeout)
      .map { analysisRepr =>
        val analysisRuns = if (includeRuns) getAnalysisRuns(analysisRepr.id, analysisRepr.name, analysisRepr.version, includeResults = false, skip = 0, limit = 500)
        else Set.empty[AnalysisRunData]

        getResultFormat(analysisRepr.formatId) match {
          case f: AnalysisResultFormat =>
            analysisRepr.toAnalysisData(f, analysisRuns)
          case _ =>
            throw new IllegalStateException("Corrupt format definition: Analysis result format must not be base value")
        }
      }.toSet
  }

  private def getInputsForRun(analysisRunId: Long): Set[SoftwareEntityData] = {
    val queryF = db.run {
      val runIdToInput = for {(ri, i) <- analysisRunInputsTable join entitiesTable on (_.inputEntityID === _.id)} yield (ri.analysisRunID, i)

      runIdToInput.filter(t => t._1 === analysisRunId).map(t => t._2).result
    }
      .map { entityReprs => buildEntities(entityReprs) }(db.ioExecutionContext)

    Await.result(queryF, longActionTimeout).toSet
  }

  private def getAnalysisRuns(analysisId: Long, analysisName: String, analysisVersion: String, includeResults: Boolean, skip: Int, limit: Int): Set[AnalysisRunData] = {

    val queryF = db
      .run(analysisRunsTable.filter(r => r.parentID === analysisId).sortBy(_.id).drop(skip).take(limit).result)
      .map { allRuns =>
        allRuns.map { run =>
          val results = if (includeResults) {
            getRunResultsAsJSON(run.uid).get
          } else Set.empty[AnalysisResultData]

          run.toAnalysisRunData(analysisName, analysisVersion, getInputsForRun(run.id), results)
        }
      }(db.ioExecutionContext)

    Await.result(queryF, longActionTimeout).toSet
  }

  override def getAnalysisRuns(analysisName: String, analysisVersion: String, includeResults: Boolean, skip: Int = 0, limit: Int = 100): Try[Set[AnalysisRunData]] = Try {
    val analysisId = getAnalysisRepr(analysisName, analysisVersion).id

    getAnalysisRuns(analysisId, analysisName, analysisVersion, includeResults, skip, limit)
  }

  override def getAnalysisRunsForEntity(entityName: String, skip: Int, limit: Int): Try[Set[AnalysisRunData]] = Try {
    val entityId = getEntityId(entityName)
    val runIdsQuery = analysisRunInputsTable.filter(_.inputEntityID === entityId).map(_.analysisRunID).result
    val runIds = Await.result(db.run(runIdsQuery), simpleQueryTimeout).distinct.sorted.slice(skip, skip + limit).toSet

    val resultF = db.run((analysisRunsTable.filter(_.id inSet runIds) join analysesTable on (_.parentID === _.id)).result)
      .map { allResults =>
        allResults.map {
          case (run, analysis) =>
            run.toAnalysisRunData(analysis.name, analysis.version, getInputsForRun(run.id), Set.empty[AnalysisResultData])
        }.toSet
      }(db.ioExecutionContext)


    Await.result(resultF, longActionTimeout)
  }

  override def getAnalysisRun(analysisName: String, analysisVersion: String, runUid: String, includeResults: Boolean = false): Try[AnalysisRunData] = Try {
    val analysisId = getAnalysisRepr(analysisName, analysisVersion).id

    val results = if (includeResults) {
      getRunResultsAsJSON(runUid).get
    } else Set.empty[AnalysisResultData]

    val queryF = db
      .run(analysisRunsTable.filter(r => r.parentID === analysisId && r.uid === runUid).take(1).result)
      .map(r => r.map(run => run.toAnalysisRunData(analysisName, analysisVersion, getInputsForRun(run.id), results)))(db.ioExecutionContext)

    Await.result(queryF, simpleQueryTimeout).head
  }

  private def getRunRepr(runUid: String): SoftwareAnalysisRunRepr = {
    val queryF = db.run(analysisRunsTable.filter(r => r.uid === runUid).take(1).result)

    Await.result(queryF, simpleQueryTimeout).headOption match {
      case Some(result) => result
      case None => throw new IllegalStateException(s"Analysis Run with uid $runUid not present in db")
    }

  }

  private def setRunState(runId: Long, runState: Int): Unit = {
    val action = db.run(analysisRunsTable.filter(r => r.id === runId).map(r => r.state).update(runState))
    Await.ready(action, simpleQueryTimeout)
  }

  override def setRunState(runUid: String, state: RunState, runInputIdsOpt: Option[Set[String]]): Try[Unit] = Try {
    val runRepr = getRunRepr(runUid)
    setRunState(runRepr.id, state.id)

    if (runInputIdsOpt.isDefined) {
      // Connect inputs to run
      val inputEntityIds = Await.result(db.run(entitiesTable.filter(e => e.qualifier inSet runInputIdsOpt.get).map(_.id).result), simpleQueryTimeout)

      val inputInsertAction = db.run(DBIO.sequence(inputEntityIds.map(id => analysisRunInputsTable += AnalysisRunInput(-1, runRepr.id, id))))
      Await.ready(inputInsertAction, simpleQueryTimeout)
    }
  }

  override def setRunResults(runUid: String,
                             timeStamp: LocalDateTime,
                             logs: Array[String],
                             freshResults: Set[AnalysisResultData],
                             unchangedResultIds: Set[String])(implicit serializer: JsonWriter[Object]): Try[Unit] = Try {

    val runRepr: SoftwareAnalysisRunRepr = getRunRepr(runUid)
    setRunState(runRepr.id, RunState.Finished.id)

    val newTimeStamp = timeStamp.format(DateTimeFormatter.ISO_DATE_TIME)
    val logsString = logs.mkString(";;;")

    val updateTimeStampAction = db.run(analysisRunsTable.filter(r => r.uid === runUid).map(r => r.timestamp).update(newTimeStamp))
    val updateLogsAction = db.run(analysisRunsTable.filter(r => r.uid === runUid).map(r => r.logs).update(logsString))

    Await.ready(updateTimeStampAction, simpleQueryTimeout)
    Await.ready(updateLogsAction, simpleQueryTimeout)

    val newResultIds = freshResults.map { runResult =>
      // Serialize result content
      val content = serializer.write(runResult.content).compactPrint
      val resultDbObj = AnalysisResult(-1, runResult.uid, runRepr.id, runResult.isRevoked, content)

      // Write result entry
      val resultDbId = Await.result(db.run(idReturningResultTable += resultDbObj), simpleQueryTimeout)

      // Connect to affected entities
      runResult.affectedEntities.map(e => getEntityRepr(e.uid, e.kind).get.id).foreach { affectedEntityId =>
        Await.ready(db.run(resultValiditiesTable += AnalysisResultValidity(-1, resultDbId, affectedEntityId)), simpleQueryTimeout)
      }

      resultDbId
    }


    val resultDbIdsAction = db.run(analysisResultsTable.filter(r => r.uid inSet unchangedResultIds).map(_.id).result)
    val unchangedResultIdsInDb = Await.result(resultDbIdsAction, simpleQueryTimeout)

    (newResultIds ++ unchangedResultIdsInDb).foreach { resultDbId =>
      Await.ready(db.run(runResultsTable += AnalysisRunResultRelation(-1, runRepr.id, resultDbId)), simpleQueryTimeout)
    }
  }

  override def getRunResultsAsJSON(runUid: String, skip: Int = 0, limit: Int = 100): Try[Set[AnalysisResultData]] = Try {

    val runRepr: SoftwareAnalysisRunRepr = getRunRepr(runUid)

    val resQuery = db.run {
      val joinQuery = for {(_, resultRepr) <- runResultsTable.filter(rr => rr.analysisRunID === runRepr.id).sortBy(_.id).drop(skip).take(limit) join analysisResultsTable on (_.resultID === _.id)} yield resultRepr

      joinQuery.result
    }

    val allResults = Await.result(resQuery, longActionTimeout)


    val resultEntitiesF = db.run {
      val join = for {(resultValidity, entity) <- resultValiditiesTable join entitiesTable on (_.entityId === _.id)}
        yield (resultValidity.resultId, entity)
      join.filter(t => t._1 inSet allResults.map(_.id).toSet).result
    }

    val resultToInputEntitiesMapping = Await.result(resultEntitiesF, longActionTimeout)

    allResults.map { resultRep =>
      val allAssociatedEntities = resultToInputEntitiesMapping
        .filter(t => t._1 == resultRep.id)
        .map(t => toGenericEntityData(t._2))

      val runIdQuery = db.run(analysisRunsTable.filter(_.id === resultRep.runId).map(_.uid).result)
      val producingRunUid = Await.result(runIdQuery, simpleQueryTimeout).head

      AnalysisResultData(resultRep.uid, resultRep.isRevoked, producingRunUid, resultRep.jsonContent, allAssociatedEntities.toSet)
    }.toSet

  }


  override def storeEmptyAnalysisRun(analysisName: String, analysisVersion: String, runConfig: String): Try[String] = Try {
    val analysisId = getAnalysisRepr(analysisName, analysisVersion).id

    // Insert run
    val timestamp = LocalDateTime.now().format(DateTimeFormatter.ISO_DATE_TIME)
    val runRepr = SoftwareAnalysisRunRepr(-1, getFreshRunUuid, runConfig, RunState.Created.id, isRevoked = false, analysisId, "", timestamp)
    Await.ready(db.run(idReturningAnalysisRunTable += runRepr), simpleQueryTimeout)

    runRepr.uid
  }

  override def getFreshResultUuids(noOfUuids: Int): Set[String] = {

    var uuids = Range(0, noOfUuids).map(_ => UUID.randomUUID().toString).toSet

    def newUuids(): Unit = uuids = Range(0, noOfUuids).map(_ => UUID.randomUUID().toString).toSet

    val query = analysisResultsTable.filter(r => r.uid inSet uuids).exists

    var uuidsFoundInDB = Await.result(db.run(query.result), simpleQueryTimeout)

    while (uuids.size < noOfUuids || uuidsFoundInDB) {
      newUuids()
      uuidsFoundInDB = Await.result(db.run(query.result), simpleQueryTimeout)
    }

    uuids
  }

  override def getFreshRunUuid: String = {
    var uuid = UUID.randomUUID().toString

    def exists: Boolean = Await.result(db.run(analysisRunsTable.filter(r => r.uid === uuid).exists.result), simpleQueryTimeout)

    while (exists) {
      uuid = UUID.randomUUID().toString
    }

    uuid
  }

  override def getJSONResultsFor(entityName: String, analysisFilter: Option[(String, String)], limit: Int, skip: Int): Try[Set[AnalysisResultData]] = Try {


    val eid = getEntityId(entityName)

    // Get all results associated with this entity
    val entityResultsF = db.run {
      val join = for {(_, result) <- resultValiditiesTable.filter(v => v.entityId === eid) join analysisResultsTable on (_.resultId === _.id)}
        yield result
      join.sortBy(_.id).drop(skip).take(limit).result
    }

    var allEntityResults = Await.result(entityResultsF, longActionTimeout)

    // Apply analysis filter
    if (analysisFilter.isDefined) {
      val analysisRepr = getAnalysisRepr(analysisFilter.get._1, analysisFilter.get._2)

      allEntityResults = allEntityResults.filter { result =>
        val analysisId = Await.result(db.run {
          analysisRunsTable.filter(run => run.id === result.runId).map(run => run.parentID).take(1).result
        }, simpleQueryTimeout).head

        analysisId == analysisRepr.id
      }
    }


    // Results may be associated with more than one entity, therefore: Collect mapping of results to entities for all results
    val resultEntitiesF = db.run {
      val join = for {(resultValidity, entity) <- resultValiditiesTable.filter(v => v.resultId inSet allEntityResults.map(_.id)) join entitiesTable on (_.entityId === _.id)}
        yield (resultValidity.resultId, entity)
      join.result
    }

    val resultToInputEntitiesMapping = Await.result(resultEntitiesF, longActionTimeout)

    // Build results
    allEntityResults.map { resultRep =>
      val allAssociatedEntities = resultToInputEntitiesMapping
        .filter(t => t._1 == resultRep.id)
        .map(t => toGenericEntityData(t._2))

      val runIdQuery = db.run(analysisRunsTable.filter(_.id === resultRep.runId).map(_.uid).result)
      val producingRunUid = Await.result(runIdQuery, simpleQueryTimeout).head

      AnalysisResultData(resultRep.uid, resultRep.isRevoked, producingRunUid, resultRep.jsonContent, allAssociatedEntities.toSet)
    }.toSet

  }

  def getAllResults(analysisName: String, analysisVersion: String, limit: Int, skip: Int): Future[Set[AnalysisResultData]] = {
    val analysisId = getAnalysisRepr(analysisName, analysisVersion).id

    val resultIdQuery = for {(_, runResultRelation) <- analysisRunsTable.filter(_.parentID === analysisId) join runResultsTable on (_.id === _.analysisRunID) }
      yield runResultRelation.resultID

    db.run(resultIdQuery.sorted.drop(skip).take(limit).result)
      .flatMap{ resultIds =>
        db.run(analysisResultsTable.filter(r => r.id inSet resultIds).result)
      }
      .flatMap{ resultsData =>
        val resultEntitiesF = db.run {
          val join = for {(resultValidity, entity) <- resultValiditiesTable.filter(v => v.resultId inSet resultsData.map(_.id)) join entitiesTable on (_.entityId === _.id)}
            yield (resultValidity.resultId, entity)
          join.result
        }

        resultEntitiesF.map(resultToEntitiesMap => (resultsData, resultToEntitiesMap))
      }
      .flatMap{ case (resultsData, resultToEntitiesMapping) =>
        val runUidMappingF = db.run(analysisRunsTable.filter(_.id inSet resultsData.map(_.runId)).map(r => (r.id, r.uid)).result)

        runUidMappingF.map(m => (resultsData, resultToEntitiesMapping, m.toMap))
      }
      .map{ case (resultsData, resultToEntitiesMapping, runToUidMapping) =>
        resultsData
          .map{ data =>
            AnalysisResultData(data.uid, data.isRevoked, runToUidMapping(data.runId), data.jsonContent, resultToEntitiesMapping.filter(_._1 == data.id).map(_._2).map(toGenericEntityData).toSet)
          }
          .toSet
      }


  }

  implicit private def tryToBool: Try[Boolean] => Boolean = {
    case Success(value) => value
    case Failure(ex) =>
      log.error("Failed to perform DB lookup", ex)
      false

  }

  override def hasAnalysis(analysisName: String): Boolean = Try {
    val queryF = db.run(analysesTable.filter(a => a.name === analysisName).exists.result)
    Await.result(queryF, simpleQueryTimeout)
  }

  override def hasAnalysisRun(analysisName: String, analysisVersion: String, runUid: String): Boolean = Try {
    val requiredId = getAnalysisRepr(analysisName, analysisVersion).id
    val queryF = db.run(analysisRunsTable.filter(r => r.uid === runUid && r.parentID === requiredId).exists.result)

    Await.result(queryF, simpleQueryTimeout)
  }


  override def isIncrementalAnalysis(analysisName: String, analysisVersion: String): Boolean = Try {
    val queryF = db.run(analysesTable.filter(a => a.name === analysisName && a.version === analysisVersion).map(_.isIncremental).result)

    val queryResult = Await.result(queryF, simpleQueryTimeout)

    queryResult.nonEmpty && queryResult.head
  }

  private[storage] def storeResultFormat(format: AnyValueFormat): Long = {
    if (format.isBaseValue) {
      format match {
        case StringFormat => ResultFormatPredef.StringFormat.id
        case NumberFormat => ResultFormatPredef.NumberFormat.id
        case EntityReferenceFormat => ResultFormatPredef.EntityRefFormat.id
        case EmptyFormat => ResultFormatPredef.EmptyFormat.id
      }
    } else {

      format match {
        case ListResultFormat(elemF, explanation) =>
          val elementFormatId = storeResultFormat(elemF)

          val formatId = Await.result(db.run(idReturningFormatTable += ResultFormat(-1, "CUSTOM_LIST", ResultType.ListResult.id)), simpleQueryTimeout)

          Await.ready(db.run(nestedResultFormatsTable += NestedResultFormatReference(formatId, elementFormatId, ResultNestingKind.ListElement.id, explanation)), simpleQueryTimeout)

          formatId

        case MapResultFormat(keyF, valueF, keyExplanation, valueExplanation) =>
          val keyFormatId = storeResultFormat(keyF)
          val valueFormatId = storeResultFormat(valueF)

          val formatId = Await.result(db.run(idReturningFormatTable += ResultFormat(-1, "CUSTOM_MAP", ResultType.MapResult.id)), simpleQueryTimeout)

          val keyAndValueInsert = DBIO.seq(nestedResultFormatsTable += NestedResultFormatReference(formatId, keyFormatId, ResultNestingKind.MapKey.id, keyExplanation),
            nestedResultFormatsTable += NestedResultFormatReference(formatId, valueFormatId, ResultNestingKind.MapValue.id, valueExplanation))

          Await.ready(db.run(keyAndValueInsert), simpleQueryTimeout)

          formatId

        case ObjectResultFormat(propFormats) =>

          val formatId = Await.result(db.run(idReturningFormatTable += ResultFormat(-1, "CUSTOM_OBJECT", ResultType.ObjectResult.id)), simpleQueryTimeout)

          propFormats.foreach { propFormat =>

            val propFormatId = storeResultFormat(propFormat)

            Await.ready(db.run(nestedResultFormatsTable += NestedResultFormatReference(formatId, propFormatId, ResultNestingKind.ObjectProperty.id, "")), simpleQueryTimeout)
          }

          formatId

        case GraphResultFormat(nodeFormats, edgeFormats, nodeDescription, edgeDescription) =>

          val formatId = Await.result(db.run(idReturningFormatTable += ResultFormat(-1, "CUSTOM_GRAPH", ResultType.GraphResult.id)), simpleQueryTimeout)

          nodeFormats.foreach { nodeProp =>
            val propFormatId = storeResultFormat(nodeProp)

            Await.ready(db.run(nestedResultFormatsTable += NestedResultFormatReference(formatId, propFormatId, ResultNestingKind.NodeProperty.id, nodeDescription)), simpleQueryTimeout)
          }

          edgeFormats.foreach { edgeProp =>
            val propFormatId = storeResultFormat(edgeProp)

            Await.ready(db.run(nestedResultFormatsTable += NestedResultFormatReference(formatId, propFormatId, ResultNestingKind.EdgeProperty.id, edgeDescription)), simpleQueryTimeout)
          }

          formatId

        case NamedPropertyFormat(propertyName, propertyFormat, explanation) =>
          val innerFormatId = storeResultFormat(propertyFormat)

          val formatId = Await.result(db.run(idReturningFormatTable += ResultFormat(-1, propertyName, ResultType.NamedPropertyResult.id)), simpleQueryTimeout)

          Await.ready(db.run(nestedResultFormatsTable += NestedResultFormatReference(formatId, innerFormatId, ResultNestingKind.NamedProperty.id, explanation)), simpleQueryTimeout)

          formatId
      }
    }

  }

  private[storage] def getResultFormat(rootId: Long): AnyValueFormat = {

    def getNestedFormats: Seq[NestedResultFormatReference] = {
      val queryF = db.run(nestedResultFormatsTable.filter(n => n.originId === rootId).result)
      Await.result(queryF, simpleQueryTimeout)
    }

    rootId match {
      // Don't need to read from DB for base values
      case ResultFormatPredef.StringFormat.id => StringFormat
      case ResultFormatPredef.NumberFormat.id => NumberFormat
      case ResultFormatPredef.EntityRefFormat.id => EntityReferenceFormat
      case ResultFormatPredef.EmptyFormat.id => EmptyFormat

      // All other ids will be some form of composite format
      case _ =>
        // Get raw format entry from DB, get list of all nested formats
        val rawFormatRepr = Await.result(db.run(resultFormatsTable.filter(f => f.id === rootId).take(1).result), simpleQueryTimeout).head
        val nestedFormats = getNestedFormats

        // Parse nested formats based on format type
        rawFormatRepr.resultType match {
          case ResultType.listTypeId if nestedFormats.size == 1 =>

            val elemFormatNesting = nestedFormats.head
            val elemFormat = getResultFormat(elemFormatNesting.targetId)
            ListResultFormat(elemFormat, elemFormatNesting.description)

          case ResultType.mapTypeId if nestedFormats.size == 2 =>

            val keyFormatNesting = nestedFormats.find(n => n.nestingKind == ResultNestingKind.MapKey.id).get
            val valueFormatNesting = nestedFormats.find(n => n.nestingKind == ResultNestingKind.MapValue.id).get

            val keyFormat = getResultFormat(keyFormatNesting.targetId)
            val valueFormat = getResultFormat(valueFormatNesting.targetId)

            if (!keyFormat.isBaseValue)
              throw new IllegalStateException("Corrupt format definition: Map key needs to be base value")

            MapResultFormat(keyFormat.asInstanceOf[BaseValueFormat], valueFormat, keyFormatNesting.description, valueFormatNesting.description)

          case ResultType.objectTypeId =>

            val objectProperties = nestedFormats.map { nesting =>
              val propFormat = getResultFormat(nesting.targetId)

              if (!propFormat.isInstanceOf[NamedPropertyFormat])
                throw new IllegalStateException("Corrupt format definition: Nested formats in object need to be Named Properties")

              propFormat.asInstanceOf[NamedPropertyFormat]
            }.toSet

            ObjectResultFormat(objectProperties)

          case ResultType.graphTypeId =>

            val nodePropNestings = nestedFormats.filter(n => n.nestingKind == ResultNestingKind.NodeProperty.id)
            val edgePropNestings = nestedFormats.filter(n => n.nestingKind == ResultNestingKind.EdgeProperty.id)

            var nodeDescription = ""

            val nodeProps = nodePropNestings.map { nesting =>
              if (nodeDescription.equals("")) nodeDescription = nesting.description
              val format = getResultFormat(nesting.targetId)


              if (!format.isInstanceOf[NamedPropertyFormat])
                throw new IllegalStateException("Corrupt format definition: Nested formats in graph nodes need to be Named Properties")

              format.asInstanceOf[NamedPropertyFormat]
            }.toSet

            var edgeDescription = ""

            val edgeProps = edgePropNestings.map { nesting =>
              if (edgeDescription.equals("")) edgeDescription = nesting.description
              val format = getResultFormat(nesting.targetId)

              if (!format.isInstanceOf[NamedPropertyFormat])
                throw new IllegalStateException("Corrupt format definition: Nested formats in graph edges need to be Named Properties")

              format.asInstanceOf[NamedPropertyFormat]
            }.toSet

            GraphResultFormat(edgeProps, nodeProps, nodeDescription, edgeDescription)

          case ResultType.namedPropTypeId if nestedFormats.size == 1 =>

            val innerFormatNesting = nestedFormats.head

            val innerFormat = getResultFormat(innerFormatNesting.targetId)

            NamedPropertyFormat(rawFormatRepr.identifier, innerFormat, innerFormatNesting.description)
        }


    }

  }
}