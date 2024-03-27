package org.anon.spareuse.execution.analyses.impl.dynamicfeatures

import org.opalj.bi.{REF_invokeInterface, REF_invokeSpecial, REF_invokeStatic, REF_invokeVirtual, REF_newInvokeSpecial}
import org.opalj.br.{InvokeSpecialMethodHandle, InvokeStaticMethodHandle, Method, MethodCallMethodHandle, MethodDescriptor}
import org.opalj.br.analyses.Project
import org.opalj.br.instructions.INVOKEDYNAMIC
import org.opalj.br.reader.InvokedynamicRewriting.{isDynamoInvokedynamic, isGroovyInvokedynamic, isJava10StringConcatInvokedynamic, isJava8LikeLambdaExpression, isObjectMethodsInvokedynamic, isScalaLambdaDeserializeExpression, isScalaStructuralCallSite, isScalaSymbolExpression}
import org.opalj.tac.{DUVar, LazyTACUsingAIKey, Stmt, TACMethodParameter, TACode}
import org.opalj.tac.cg.CallGraph
import org.opalj.value.ValueInformation
import org.opalj.br.ObjectType.LambdaMetafactory

class Invokedynamics {

  //var rewriteInvokeDynamic = false
  type V = DUVar[ValueInformation]

  var result: Set[FeatureContainer] = Set.empty

  def apply[S](project: Project[S], cg: CallGraph): Set[FeatureContainer] = {

    val classFileVersion = project.allClassFiles.head.jdkVersion

    implicit val tac: Method => TACode[TACMethodParameter, V] = {
        project.get(LazyTACUsingAIKey)
    }

    for (rm <- cg.reachableMethods()) {

      for (caller <- cg.callersOf(rm.method)) {
         if(caller._1.definedMethod.body.nonEmpty){
            val tacApplied = try {

              tac.apply(caller._1.definedMethod)

            } catch {
              /*case e1: UnsupportedOperationException =>
                logger.info("UnsupportedOperationException")
                throw new UnsupportedOperationException()*/
              case e: Exception =>
                throw e
            }

            val pc = caller._2
            if (caller._1.definedMethod.body.get.lineNumber(pc).nonEmpty) {
              val linenumber = caller._1.definedMethod.body.get.lineNumber(pc).get
              val host = caller._1.definedMethod.classFile

              implicit val body: Array[
                Stmt[V]] = tacApplied.stmts

              val methodBody = caller._1.definedMethod.body
              for (i <- methodBody.toList) {
                i.instructions.toList.foreach(m => m match {
                  case in: INVOKEDYNAMIC =>

                    if (isScalaLambdaDeserializeExpression(in) ||
                      isScalaSymbolExpression(in) ||
                      (caller._1.definedMethod.instructionsOption.nonEmpty &&
                        isScalaStructuralCallSite(in, caller._1.definedMethod.instructionsOption.get, pc)) ||
                      isGroovyInvokedynamic(in) ||
                      isDynamoInvokedynamic(in) ||
                      isJava10StringConcatInvokedynamic(in) ||
                      isObjectMethodsInvokedynamic(in)
                    ) {
                      val bm = in.bootstrapMethod
                      val handle = bm.arguments(1).asInstanceOf[MethodCallMethodHandle]
                      result += FeatureContainer("Invokedynamics Lambda", rm.method.name, rm.method.declaringClassType.fqn,
                        pc, linenumber, caller._1.name, "instruction name: " + in.name + "  and handle name: " + handle.name, host.fqn, classFileVersion)
                    }

                    else if (isJava8LikeLambdaExpression(in)) {
                      val bm = in.bootstrapMethod
                      val handle = bm.arguments(1).asInstanceOf[MethodCallMethodHandle]

                      val InvokeStaticMethodHandle(LambdaMetafactory, false, name, descriptor) = bm.handle
                      if (descriptor == MethodDescriptor.LambdaAltMetafactoryDescriptor &&
                        name == "altMetafactory") {
                        result += FeatureContainer("Invokedynamics Lambda", rm.method.name, rm.method.declaringClassType.fqn,
                          pc, linenumber, caller._1.name, "instruction name: " + in.name + " and handle name: " + handle.name, host.fqn, classFileVersion)
                      }
                      // for Lambda-related, some cases may be missing

                      handle.referenceKind match {
                        case REF_invokeInterface | REF_invokeVirtual | REF_newInvokeSpecial =>
                          result += FeatureContainer("Invokedynamics MethodReferences", rm.method.name, rm.method.declaringClassType.fqn,
                            pc, linenumber, caller._1.name, "instruction name: " + in.name + " and handle name: " + handle.name, host.fqn, classFileVersion)
                        case REF_invokeStatic => {
                          val InvokeStaticMethodHandle(_, _, name, methodDes) = handle
                          val localMethod = caller._1.definedMethod.classFile.findMethod(name, methodDes)
                          if (localMethod.isDefined) {
                            val callee = localMethod.get
                            if (callee.isStatic) {
                              if (callee.isSynthetic) {
                                result += FeatureContainer("Invokedynamics Lambda", rm.method.name, rm.method.declaringClassType.fqn,
                                  pc, linenumber, caller._1.name, "instruction name: " + in.name + " and handle name: " + handle.name, host.fqn, classFileVersion)
                              }
                              else {
                                result += FeatureContainer("Invokedynamics MethodReferences", rm.method.name, rm.method.declaringClassType.fqn,
                                  pc, linenumber, caller._1.name, "instruction name: " + in.name + "  and handle name: " + handle.name, host.fqn, classFileVersion)
                              }
                            }
                          }
                          else {
                            result += FeatureContainer("Invokedynamics Lambda", rm.method.name, rm.method.declaringClassType.fqn,
                              pc, linenumber, caller._1.name, "instruction name: " + in.name + "  and handle name: " + handle.name, host.fqn, classFileVersion)
                          }
                        }
                        case REF_invokeSpecial => {
                          val InvokeSpecialMethodHandle(_, isInterface, name, methodDes) = handle
                          val localMethod = caller._1.definedMethod.classFile.findMethod(name, methodDes)
                          if (localMethod.isDefined) {
                            result += FeatureContainer("Invokedynamics MethodReferences", rm.method.name, rm.method.declaringClassType.fqn,
                              pc, linenumber, caller._1.name, "instruction name: " + in.name + "  and handle name: " + handle.name, host.fqn, classFileVersion)
                          }
                        }
                        case _ =>
                      }

                    }
                    else {
                      val bm = in.bootstrapMethod
                      val handle = bm.arguments(1).asInstanceOf[MethodCallMethodHandle]
                      result += FeatureContainer("Invokedynamics Other", rm.method.name, rm.method.declaringClassType.fqn,
                        pc, linenumber, caller._1.name, "instruction name: " + in.name + "  and handle name: " + handle.name, host.fqn, classFileVersion)
                    }
                  case _ =>
                })
              }
            }
          }
      }
    }
    result
  }

}
