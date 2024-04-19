package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.br.MethodDescriptor.{JustReturnsObject, ReadObjectDescriptor, WriteObjectDescriptor}
import org.opalj.br.{Method, MethodCallMethodHandle, MethodDescriptor, ObjectType, ReferenceType}
import org.opalj.br.analyses.{Project, SomeProject}
import org.opalj.tac.{Assignment, DUVar, ExprStmt, InvokedynamicFunctionCall, LazyTACUsingAIKey, TACMethodParameter, TACode, VirtualMethodCall}
import org.opalj.tac.cg.CallGraph
import org.opalj.value.ValueInformation

import scala.annotation.switch

class Serialization {

  val OOSType = ObjectType("java/io/ObjectOutputStream")
  val OISType = ObjectType("java/io/ObjectInputStream")

  type V = DUVar[ValueInformation]

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    implicit val tac: Method => TACode[TACMethodParameter, V] =
      project.get(LazyTACUsingAIKey)

    val serializableTypes: Set[ObjectType] = project.classHierarchy.allSubtypes(ObjectType.Serializable, false)
    val externalizableTypes: Set[ObjectType] = project.classHierarchy.allSubtypes(ObjectType.Externalizable, false)

    for (rm <- cg.reachableMethods()) {

      (rm.method.declaringClassType.fqn: @switch) match {
        case OOSType.fqn => rm.method.name match {
          case "writeObject" =>

            for (caller <- cg.callersOf(rm.method)) {
              val tacApplied = try {
                tac.apply(caller._1.definedMethod)
              } catch {
                /*case e1: UnsupportedOperationException =>
                  throw new UnsupportedOperationException()*/
                case e: Exception =>
                  throw e
              }

              val pc = caller._2
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              val invocation = tacApplied.stmts(tacApplied.properStmtIndexForPC(pc))

              if (invocation.astID == VirtualMethodCall.ASTID) {
                val paramVar = invocation.asVirtualMethodCall.params.head.asVar
                if(paramVar.value.isReferenceValue){
                  val param = paramVar.value.asReferenceValue


                  if (project.classHierarchy.isSubtypeOf(param.asReferenceType, ObjectType.Externalizable)) {
                    result += FeatureContainer("Serialization Externalizable", rm.method.name, rm.method.declaringClassType.fqn,
                      pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
                  }

                  if (!project.classHierarchy.isSubtypeOf(
                    param.asReferenceType, ObjectType.Externalizable)) {
                    result += FeatureContainer("Serialization", rm.method.name, rm.method.declaringClassType.fqn,
                      pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
                  }
                }
              }
            }
          case _ =>
        }

        case OISType.fqn => rm.method.name match {
          case "readObject" => {

            if (rm.method.isVirtualOrHasSingleDefinedMethod) {

              for (caller <- cg.callersOf(rm.method)) {
                val tacApplied = try {
                  tac.apply(caller._1.definedMethod)
                } catch {
                  /*case e1: UnsupportedOperationException =>
                    throw new UnsupportedOperationException()*/
                  case e: Exception =>
                    throw e
                }

                val pc = caller._2
                val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
                val invocation = tacApplied.stmts(tacApplied.properStmtIndexForPC(pc))

                if (invocation.astID == Assignment.ASTID | (invocation.astID == ExprStmt.ASTID)) {

                  if (serializableTypes.exists {
                    subtype => {
                      if (subtype.asReferenceType.isObjectType) {
                        val ot = subtype.asReferenceType.asObjectType
                        val cf = project.classFile(ot)
                        cf.isDefined && cf.get.findMethod("readObject", ReadObjectDescriptor).isDefined ||
                          project.instanceCall(ot, ot, "readObject", ReadObjectDescriptor).hasValue ||
                          cf.isDefined && cf.get.findMethod("readResolve", JustReturnsObject).isDefined ||
                          project.instanceCall(ot, ot, "readResolve", JustReturnsObject).hasValue
                      }
                      else false
                    }
                  }) {
                    result += FeatureContainer("Serialization", rm.method.name, rm.method.declaringClassType.fqn,
                      pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
                  }

                  else if (externalizableTypes.nonEmpty) {
                    result += FeatureContainer("Serialization Externalizable", rm.method.name, rm.method.declaringClassType.fqn,
                      pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
                  }
                }
              }
            }
          }

          case "registerValidation" => {

            if (rm.method.isVirtualOrHasSingleDefinedMethod) {

              for (caller <- cg.callersOf(rm.method)) {
                val tacApplied = try {
                  tac.apply(caller._1.definedMethod)
                } catch {
                  /*case e1: UnsupportedOperationException =>
                    throw new UnsupportedOperationException()*/
                  case e: Exception =>
                    throw e
                }

                val pc = caller._2
                val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
                val invocation = tacApplied.stmts(tacApplied.properStmtIndexForPC(pc))

                if (invocation.astID == VirtualMethodCall.ASTID) {
                  result += FeatureContainer("Serialization", rm.method.name, rm.method.declaringClassType.fqn,
                    pc, linenumber, caller._1.name, "", "", classFileVersion, cg.reachableMethods().size)
                }
              }
            }
          }

          case _ =>
        }
        case _ =>
        /*rm.method.name match {
          case "readResolve" => result += FeatureContainer("Serialization readResolve", rm.method.name, 0, 0)
          case _ =>
        }*/
      }
    }
    result
  }
}
