package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.anon.spareuse.execution.analyses.{AnalysisResult, FreshResult}
import org.opalj.ai.domain.l1.ArrayValues
import org.opalj.br.{Method, ObjectType}
import org.opalj.br.analyses.{Project, SomeProject}
import org.opalj.br.instructions.{INVOKEVIRTUAL, Instruction}
import org.opalj.collection.immutable.IntTrieSet
import org.opalj.tac.{ArrayLoad, ArrayStore, Assignment, Checkcast, Compare, DUVar, ExprStmt, FunctionCall, GetField, If, InstanceOf, LazyTACUsingAIKey, MonitorEnter, MonitorExit, New, NonVirtualFunctionCall, NonVirtualMethodCall, PutField, StaticFunctionCall, StaticMethodCall, Stmt, TACMethodParameter, TACode, VirtualFunctionCall, VirtualMethodCall}
import org.opalj.tac.cg.CallGraph
import org.opalj.value.ValueInformation

import java.io.File
import scala.collection.mutable.ListBuffer

class ReflectionFeature {

  // constants
  val TrivialReflReflectionClass = "java/lang/reflect/Method"
  val MethodType = ObjectType("java/lang/reflect/Method")
  val ClassType = /*ObjectType("java/lang/Class")*/ ObjectType.Class
  val ConstructorType = ObjectType("java/lang/reflect/Constructor")
  val FieldType = ObjectType("java/lang/reflect/Field")
  val TrivialReflInvoke = "invoke"
  val TrivialReflGetMethod = "getMethod"
  val ConstrucorNewInstance = "newInstance"
  val TrivialReflClass = "java/lang/Class"
  val TrivialReflForName = "forName" // examplified usage for Class.forName trivial reflection
  val TrivialReflDeclaredMethod = "getDeclaredMethod"
  val TrivialReflGetField = "getField"

  type V = DUVar[ValueInformation]

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph, publishedAt: String): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    implicit val tac: Method => TACode[TACMethodParameter, V] =
      project.get(LazyTACUsingAIKey)

    for (r <- cg.reachableMethods()) {   //TODO

      (r.method.declaringClassType.fqn /*: @switch*/) match {
        case MethodType.fqn => r.method.name match {
          case "invoke" =>

            for (y <- cg.callersOf(r.method)) {
              val tacApplied = try {
                tac.apply(y._1.definedMethod)
              } catch {
                /*case e1: UnsupportedOperationException =>
                  logger.info("UnsupportedOperationException")
                  throw new UnsupportedOperationException()*/
                case e: Exception =>
                  throw e
              }

              val pc = y._2
              var linenumber = 0
              if (y._1.definedMethod.body.get.lineNumber(pc).isDefined) {
                linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
              }

              val host = y._1.definedMethod.classFile
              implicit val body: Array[Stmt[V]] = tacApplied.stmts
              val index = tacApplied.properStmtIndexForPC(pc)

              if (index != -1) {
                val stmt = tacApplied.stmts(index)

                val call: FunctionCall[V] = {
                  if (stmt.isAssignment) {
                    stmt.asAssignment.expr.asFunctionCall.asVirtualFunctionCall
                  }
                  else if (stmt.isExprStmt) {
                    stmt.asExprStmt.expr.asFunctionCall.asVirtualFunctionCall
                  }
                  else {
                    null
                  }
                }

                //TODO check
                // evtl. hier einiges unnötig. Kann ich u.a die checks auf die params vermeiden? debuggen
                //call.declaringClass match {
                //case MethodType =>
                //call.asVirtualFunctionCall
                //if (call.params.head.asVar.value.asReferenceValue.isNull.isYes ||
                //call.params.head.asVar.value.asReferenceValue.isNull.isNo){
                if (call.params.head.asVar.value.isReferenceValue) {

                  result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                    pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                }
                else {
                  //result += FeatureContainer("Trivial Reflection", r.method.name, pc, linenumber)
                }

                // second param is string, represents method's parameter
                // need to generalize for invoking methods that have more than one parameter? try another test, maybe args need to be array then
                if(call.isVirtualFunctionCall){
                  if(!call.asVirtualFunctionCall.params.isEmpty){
                    if(call.asVirtualFunctionCall.params.size > 1){
                      if (call.asVirtualFunctionCall.params(1).isVar) {
                        val paramTypes = call.asVirtualFunctionCall.params(1).asVar.value
                        if (paramTypes.asReferenceValue.allValues.exists { v =>
                          // unsure about both variants
                          v.isNull.isNoOrUnknown
                        }) {
                          result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                            pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                        }
                        /*if (paramTypes.asReferenceValue.allValues.exists { v =>
                          if(v.isNull.isNoOrUnknown){
                            v.asInstanceOf[ArrayValues#DomainArrayValue].length.contains(0)
                          }
                          else{v.isNull.isNo}
                        }) {
                          result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                            pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size)
                        }*/
                      }
                    }
                  }
                }
              }
            }
          case "setAccessible" => {
            for (y <- cg.callersOf(r.method)) {
              val tacApplied = try {
                tac.apply(y._1.definedMethod)
              } catch {
                /*case e1: UnsupportedOperationException =>
                  logger.info("UnsupportedOperationException")
                  throw new UnsupportedOperationException()*/
                case e: Exception =>
                  throw e
              }

              val pc = y._2
              val linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
              val host = y._1.definedMethod.classFile
              implicit val body: Array[Stmt[V]] = tacApplied.stmts
              val index = tacApplied.properStmtIndexForPC(pc)

              if (index != -1) {
                val stmt = tacApplied.stmts(index)

                if (stmt.isVirtualMethodCall) {
                  result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                    pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                }
              }
            }
          }
          case _ =>
        }
        case ConstructorType.fqn => r.method.name match {
          case "newInstance" => {
            for (y <- cg.callersOf(r.method)) {

              val pc = y._2
              var linenumber = 0
              if (y._1.definedMethod.body.get.lineNumber(pc).isDefined) {
                linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
              }
              else{
                linenumber = 0
              }

              val host = y._1.definedMethod.classFile

              result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
            }
          }
          case "setAccessible" => {}
          case _ =>

        }
        case ClassType.fqn => r.method.name match {
          case "newInstance" => {
            for (y <- cg.callersOf(r.method)) {

              val pc = y._2
              var linenumber = 0
              if (y._1.definedMethod.body.get.lineNumber(pc).isDefined) {
                linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
              }

              val host = y._1.definedMethod.classFile
              result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
            }
          }

          case "getMethod" | "getMethods" | "getDeclaredMethod" | "getDeclaredMethods" => {
            for (y <- cg.callersOf(r.method)) {
              val tacApplied4 = try {
                tac.apply(y._1.definedMethod)
              } catch {
                /*case e1: UnsupportedOperationException =>
                  throw new UnsupportedOperationException()*/
                case e: Exception =>
                  throw e
              }

              val pc = y._2
              var linenumber = 0
              if (y._1.definedMethod.body.get.lineNumber(pc).isDefined) {
                linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
              }
              else{
                linenumber = 0
              }

              val host = y._1.definedMethod.classFile

              implicit val body: Array[Stmt[V]] = tacApplied4.stmts
              val index = tacApplied4.properStmtIndexForPC(pc)

              if (index != -1) {
                val stmt = tacApplied4.stmts(index)

                val call: FunctionCall[V] = {
                  if (stmt.isAssignment) {
                    stmt.asAssignment.expr.asFunctionCall
                  }
                  else if (stmt.isExprStmt) {
                    stmt.asExprStmt.expr.asFunctionCall
                  }
                  else {
                    null
                  }
                }

                // check invoke called directly
                var getMethodDirectInvoke = false
                var methodUsedForNonDirectInvocation = false
                if(stmt.isAssignment){
                  if (stmt.asAssignment.targetVar.usedBy.exists { useSite =>
                    val stmt = body(useSite)
                    stmt.astID match {
                      case Assignment.ASTID =>
                        stmt.asAssignment.expr.isVirtualFunctionCall &&
                          stmt.asAssignment.expr.asVirtualFunctionCall.name == "invoke"
                      case ExprStmt.ASTID =>
                        stmt.asExprStmt.expr.isVirtualFunctionCall &&
                          stmt.asExprStmt.expr.asVirtualFunctionCall.name == "invoke"
                      case _ => false
                    }
                  }) {
                    getMethodDirectInvoke = true
                  }

                  else {
                    if(stmt.asAssignment.targetVar != null){
                      methodUsedForNonDirectInvocation =
                        stmt.asAssignment.targetVar.usedBy.exists { useSite =>
                          val stmt = body(useSite)
                          stmt.astID match {
                            case VirtualMethodCall.ASTID | NonVirtualMethodCall.ASTID | StaticMethodCall.ASTID =>
                              if(stmt.isAssignment){
                                if (stmt.asAssignment.expr.isFunctionCall) {
                                  if (stmt.asAssignment.expr.asFunctionCall.params.exists(_.asVar.definedBy.contains(index))
                                    && nonLocalCallInProject(MethodType, "invoke", project)) {
                                    true
                                  }
                                  else
                                    false
                                }
                                else false
                              }
                              else false

                            case Assignment.ASTID =>
                              stmt.asAssignment.expr.astID match {
                                case VirtualFunctionCall.ASTID | NonVirtualMethodCall.ASTID | StaticFunctionCall.ASTID =>
                                  if (stmt.asAssignment.expr.asFunctionCall.params.exists(_.asVar.definedBy.contains(index))
                                    && nonLocalCallInProject(MethodType, "invoke", project)) {
                                    true
                                  } else {
                                    false
                                  }
                                case InstanceOf.ASTID | Compare.ASTID => false
                                case _ => nonLocalCallInProject(MethodType, "invoke", project)
                              }
                            case ExprStmt.ASTID =>
                              stmt.asExprStmt.expr.astID match {
                                case VirtualFunctionCall.ASTID | NonVirtualFunctionCall.ASTID | StaticFunctionCall.ASTID =>
                                  // mayUse mayUse(stmt.asExprStmt.expr.asFunctionCall.params, pc)
                                  if (stmt.asExprStmt.expr.asFunctionCall.params.exists(_.asVar.definedBy.contains(index))
                                    && nonLocalCallInProject(MethodType, "invoke", project)) {
                                    true
                                  }
                                  else
                                    false
                                case InstanceOf.ASTID | Compare.ASTID => false
                                case _ => nonLocalCallInProject(MethodType, "invoke", project)

                              }
                            case MonitorEnter.ASTID | MonitorExit.ASTID | If.ASTID | Checkcast.ASTID => false
                            case _ => nonLocalCallInProject(MethodType, "invoke", project)
                          }
                        }
                    }
                  }
                }

                if (stmt.astID == Assignment.ASTID && getMethodDirectInvoke) {
                  //handle parameters, wichtig wegen user input category e.g.!
                  if(!call.params.isEmpty){
                    val definedBy = call.params.head.asVar.definedBy
                    // check if param trivial string constant
                    if (simpleDefinition(definedBy, body).exists(_.expr.isConst)) {
                      result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                        pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                    }
                    else {
                      definedBy.foreach { defSite =>
                        if (defSite < 0) {
                          result += FeatureContainer("Non-Trivial Reflection (user input(only?))", r.method.name, r.method.declaringClassType.fqn,
                            pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                        } else { // maybe irrelevant?
                          //val definitionExpr = body(defSite).asAssignment.expr
                          //if (definitionExpr.isConst) {
                          // test case LRR1, multiple constants
                          //roughly say non-trivial, maybe enhance later
                          result += FeatureContainer("Non-Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                            pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                          //}
                        }
                      }
                    }
                  }
                }
                else if (stmt.astID == Assignment.ASTID && methodUsedForNonDirectInvocation) {
                  result += FeatureContainer("Non-Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                    pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                }
              }
            }
          }
          case "getField" | "getFields" | "getDeclaredField" | "getDeclaredFields" => {
            for (y <- cg.callersOf(r.method)) {
              val tacApplied = try {
                tac.apply(y._1.definedMethod)
              } catch {
                /*case e1: UnsupportedOperationException =>
                  throw new UnsupportedOperationException()*/
                case e: Exception =>
                  throw e
              }

              val pc = y._2
              var linenumber = 0
              if (y._1.definedMethod.body.get.lineNumber(pc).isDefined) {
                linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
              }

              val host = y._1.definedMethod.classFile
              implicit val body: Array[Stmt[V]] = tacApplied.stmts
              val index = tacApplied.properStmtIndexForPC(pc)

              if (index != -1) {
                val stmt = tacApplied.stmts(index)

                val call: FunctionCall[V] = {
                  if (stmt.isAssignment) {
                    stmt.asAssignment.expr.asFunctionCall
                  }
                  else {
                    stmt.asExprStmt.expr.asFunctionCall
                  }
                }

                var fieldGetUsedForInvocation = false
                var fieldGetUsedForNonDirectInvocation = false
                if (stmt.asAssignment.targetVar.usedBy.exists {
                  useSite =>
                    val stmtUse = body(useSite)
                    stmtUse.astID match {
                      case Assignment.ASTID => {
                        var checkFieldUsedDirectly = false
                        if(stmtUse.isAssignment){
                          checkFieldUsedDirectly = if (stmtUse.asAssignment.targetVar.usedBy.exists {
                            innerUseSite =>
                              val stmt = body(innerUseSite)
                              stmt.astID match {
                                case VirtualMethodCall.ASTID =>
                                  stmt.asVirtualMethodCall.receiver.asVar.definedBy.contains(useSite)
                                case Assignment.ASTID =>
                                  stmt.asAssignment.expr.isVirtualFunctionCall &&
                                    stmt.asAssignment.expr.asVirtualFunctionCall.receiver.asVar.definedBy.contains(useSite)
                                case ExprStmt.ASTID =>
                                  stmt.asExprStmt.expr.isVirtualFunctionCall &&
                                    stmt.asExprStmt.expr.asVirtualFunctionCall.receiver.asVar.definedBy.contains(useSite)
                                case _ => false
                              }
                          }) {
                            true
                          } else false
                          stmtUse.asAssignment.expr.isVirtualFunctionCall &&
                            stmtUse.asAssignment.expr.asVirtualFunctionCall.name == "get" &&
                            checkFieldUsedDirectly
                        }
                        else{false}

                      }  //TODO

                      case ExprStmt.ASTID => {
                        var checkFieldUsedDirectly = false
                        if(stmtUse.isAssignment){
                          checkFieldUsedDirectly = if (stmtUse.asAssignment.targetVar.usedBy.exists {
                            innerUseSite =>
                              val stmt = body(innerUseSite)
                              stmt.astID match {
                                case VirtualMethodCall.ASTID =>
                                  stmt.asVirtualMethodCall.receiver.asVar.definedBy.contains(pc)
                                case Assignment.ASTID =>
                                  stmt.asAssignment.expr.isVirtualFunctionCall &&
                                    stmt.asAssignment.expr.asVirtualFunctionCall.receiver.asVar.definedBy.contains(pc)
                                case ExprStmt.ASTID =>
                                  stmt.asExprStmt.expr.isVirtualFunctionCall &&
                                    stmt.asExprStmt.expr.asVirtualFunctionCall.receiver.asVar.definedBy.contains(pc)
                                case _ => false
                              }
                          }) {
                            true
                          } else false
                        }

                        stmtUse.asExprStmt.expr.isVirtualFunctionCall &&
                          stmtUse.asExprStmt.expr.asVirtualFunctionCall.name == "get" &&
                          checkFieldUsedDirectly
                      }
                      case _ => false
                    }
                }) {
                  fieldGetUsedForInvocation = true
                }
                else {
                  // need to check that get is called but not directly
                  // hier fehlt evtl noch der Fall, dass auch der value escapen kann, aber evtl. ziemlicher edge case
                  fieldGetUsedForNonDirectInvocation =
                    stmt.asAssignment.targetVar.usedBy.exists {
                      useSite =>
                        val stmt = body(useSite)
                        stmt.astID match {
                          case VirtualMethodCall.ASTID | NonVirtualMethodCall.ASTID |
                               StaticMethodCall.ASTID =>
                            stmt.asMethodCall.params.exists(_.asVar.definedBy.contains(pc)) &&
                              nonLocalCallInProject(FieldType, "get", project)
                          case Assignment.ASTID =>
                            stmt.asAssignment.expr.astID match {
                              case VirtualFunctionCall.ASTID | NonVirtualFunctionCall.ASTID |
                                   StaticFunctionCall.ASTID =>
                                stmt.asAssignment.expr.asFunctionCall.params.exists(_.asVar.definedBy.contains(pc)) &&
                                  nonLocalCallInProject(FieldType, "get", project)
                              case InstanceOf.ASTID | Compare.ASTID => false
                              case _ => nonLocalCallInProject(FieldType, "get", project)
                            }
                          case ExprStmt.ASTID =>
                            stmt.asExprStmt.expr.astID match {
                              case VirtualFunctionCall.ASTID | NonVirtualFunctionCall.ASTID |
                                   StaticFunctionCall.ASTID =>
                                stmt.asExprStmt.expr.asFunctionCall.params.exists(_.asVar.definedBy.contains(pc)) &&
                                  nonLocalCallInProject(FieldType, "get", project)
                              case InstanceOf.ASTID | Compare.ASTID => false
                              case _ => nonLocalCallInProject(FieldType, "get", project)
                            }
                          case _ => false
                        }
                    }
                }

                if(!call.params.isEmpty){
                  val definedBy = call.params.head.asVar.definedBy
                  if (stmt.astID == Assignment.ASTID && fieldGetUsedForInvocation) {
                    // check if param trivial string constant
                    if (simpleDefinition(definedBy, body).exists(_.expr.isConst)) {
                      result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                        pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                    }
                    else {
                      definedBy.foreach { defSite =>
                        if (defSite < 0) {
                          // need to check with custom test case
                          result += FeatureContainer("Non-Trivial Reflection (user input (only?))", r.method.name, r.method.declaringClassType.fqn,
                            pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                        }
                      }
                    }
                  }

                  else {
                    if (stmt.astID == Assignment.ASTID && fieldGetUsedForNonDirectInvocation) {
                      result += FeatureContainer("Non-Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                        pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                    }
                  }
                }

              }
            }  //TODO

          }
          case "forName" => {
            for (y <- cg.callersOf(r.method)) {
              val tacApplied = try {
                tac.apply(y._1.definedMethod)
              } catch {
                /*case e1: UnsupportedOperationException =>
                  throw new UnsupportedOperationException()*/
                case e: Exception =>
                  throw e //TODO
              }

              val pc = y._2
              if (y._1.definedMethod.body.get.lineNumber(pc).isDefined) {
                val linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
                val host = y._1.definedMethod.classFile
                implicit val body: Array[Stmt[V]] = tacApplied.stmts
                val index = tacApplied.properStmtIndexForPC(pc)

                // index is pc
                if (index != -1) {
                  val stmt = tacApplied.stmts(index)

                  val call: FunctionCall[V] = {
                    if (stmt.isAssignment) {
                      if (stmt.asAssignment.expr.isFunctionCall) {
                        stmt.asAssignment.expr.asFunctionCall
                      }
                      else {
                        null
                      }
                    }
                    else {
                      stmt.asExprStmt.expr.asFunctionCall
                    }
                  }

                  if (call != null) {
                    val definedBy = call.params.head.asVar.definedBy
                    if (simpleDefinition(definedBy, body).exists(_.expr.isConst)) {
                      result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                        pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                    } else {
                      definedBy.foreach { defSite =>
                        if (defSite < 0) {
                          // need to check with custom test case
                          result += FeatureContainer("Non-Trivial Reflection (user input (only?))", r.method.name, r.method.declaringClassType.fqn,
                            pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                        }
                        else result += FeatureContainer("Non-Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                          pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                      }
                    }
                  }
                }
              }
            }
          }
          case _ =>
        }

        case FieldType.fqn =>
          for (y <- cg.callersOf(r.method)) {
            val tacApplied = try {
              tac.apply(y._1.definedMethod)
            } catch {
              /*case e1: UnsupportedOperationException =>
                throw new UnsupportedOperationException()*/
              case e: Exception =>
                throw e
            }

            val pc = y._2
            if(y._1.hasSingleDefinedMethod){
              if (y._1.definedMethod.body != null) {
                if(y._1.definedMethod.body.get.lineNumber(pc).isDefined){
                  val linenumber = y._1.definedMethod.body.get.lineNumber(pc).get
                  val host = y._1.definedMethod.classFile
                  implicit val body: Array[Stmt[V]] = tacApplied.stmts
                  val index = tacApplied.properStmtIndexForPC(pc)

                  if (index != -1) {
                    val stmt = tacApplied.stmts(index)

                    var checkFieldUsedDirectly = false
                    var fieldUsedForNonDirectInvocation = false
                    if (stmt.isAssignment) {
                      checkFieldUsedDirectly = if (stmt.asAssignment.targetVar.usedBy.exists {
                        innerUseSite =>
                          val stmtUse = body(innerUseSite)
                          stmt.astID match {
                            case VirtualMethodCall.ASTID =>
                              stmt.asVirtualMethodCall.receiver.asVar.definedBy.contains(pc)
                            case Assignment.ASTID =>
                              stmt.asAssignment.expr.isVirtualFunctionCall &&
                                stmt.asAssignment.expr.asVirtualFunctionCall.receiver.asVar.definedBy.contains(pc)
                            case ExprStmt.ASTID =>
                              stmt.asExprStmt.expr.isVirtualFunctionCall &&
                                stmt.asExprStmt.expr.asVirtualFunctionCall.receiver.asVar.definedBy.contains(pc)
                            case _ => false
                          }
                      }) {
                        true
                      } else false
                    }

                    // value escaped
                    if (stmt.isAssignment) {
                      fieldUsedForNonDirectInvocation =
                        stmt.asAssignment.targetVar.usedBy.exists {
                          useSite =>
                            val stmt = body(useSite)
                            stmt.astID match {
                              case PutField.ASTID => stmt.asPutField.value.asVar.definedBy.contains(pc)
                              case ArrayStore.ASTID => stmt.asArrayStore.value.asVar.definedBy.contains(pc)
                              case Assignment.ASTID =>
                                stmt.asAssignment.expr.astID match {
                                  case InstanceOf.ASTID | Compare.ASTID | GetField.ASTID |
                                       ArrayLoad.ASTID => false
                                  case _ => true
                                }
                              case MonitorEnter.ASTID | MonitorExit.ASTID | If.ASTID | Checkcast.ASTID => false
                              case _ => true
                            }
                        }
                    }

                    if (stmt.astID == Assignment.ASTID && checkFieldUsedDirectly) {
                      result += FeatureContainer("Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                        pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                    }
                    else if (stmt.astID == Assignment.ASTID && fieldUsedForNonDirectInvocation) {
                      result += FeatureContainer("Non-Trivial Reflection", r.method.name, r.method.declaringClassType.fqn,
                        pc, linenumber, y._1.name, "", host.fqn, classFileVersion, cg.reachableMethods().size, publishedAt)
                    }
                  }
                }
              }
            }
          }
        case _ =>
      }
    }
    result

  }

  def simpleDefinition(definedBy: IntTrieSet, body: Array[Stmt[V]]): Option[Assignment[V]] = {
    // unsicher, ob >= 0 richtig oder ob doch einfach >0 sein sollte, werde es aber eh vereinfachen
    if (definedBy.size == 1 && definedBy.head >= 0 &&
      body(definedBy.head).astID == Assignment.ASTID) {
      Some(body(definedBy.head).asAssignment)
    }
    else None
  }

  def nonLocalCallInProject(ot: ObjectType, name: String, project: SomeProject): Boolean = {
    implicit val tac: Method => TACode[TACMethodParameter, V] =
      project.get(LazyTACUsingAIKey)

    project.allMethodsWithBody.exists {
      method =>
        val invokes = method.body.get.collect({
          case i@INVOKEVIRTUAL(`ot`, `name`, _) => i
        }: PartialFunction[Instruction, INVOKEVIRTUAL])
        if (invokes.isEmpty) {
          false
        } else {
          val tacApply = tac(method)
          val stmts = tacApply.stmts
          invokes.exists { pcAndInvocation =>
            val stmt = stmts(tacApply.properStmtIndexForPC(pcAndInvocation.pc))
            val call =
              if (stmt.astID == Assignment.ASTID)
                stmt.asAssignment.expr.asVirtualFunctionCall
              else
                stmt.asExprStmt.expr.asVirtualFunctionCall
            call.receiver.asVar.definedBy.exists { defSite =>
              defSite < 0 || stmts(defSite).astID != New.ASTID
            }
          }
        }
    }
  }
}
