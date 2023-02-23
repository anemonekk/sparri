package de.tudo.sse.spareuse.core.model.entities

import de.tudo.sse.spareuse.core.model.SoftwareEntityKind
import de.tudo.sse.spareuse.core.model.SoftwareEntityKind.SoftwareEntityKind
import de.tudo.sse.spareuse.core.model.entities.JavaEntities.JavaFieldAccessType.JavaFieldAccessType
import de.tudo.sse.spareuse.core.model.entities.JavaEntities.JavaInvocationType.JavaInvocationType

object JavaEntities {

  def buildLibrary(ga: String, repoIdent: String = "mvn"): JavaLibrary = new JavaLibrary(ga, repoIdent)

  def buildProgram(gav: String, repoIdent: String = "mvn", hash: Array[Byte] = Array.empty): JavaProgram = {
    buildProgramFor(buildLibrary(gav.substring(0, gav.lastIndexOf(":")), repoIdent), gav, hash)
  }

  def buildProgramFor(jl: JavaLibrary, gav: String, hash: Array[Byte] = Array.empty): JavaProgram = {
    val ident = jl.uid + "!" + gav
    val jp = new JavaProgram(gav, gav, ident, jl.repository, hash)
    jp.setParent(jl)
    jp
  }

  def buildPackage(gav: String, packageName: String, repoIdent: String = "mvn"): JavaPackage = {
    buildPackageFor(buildProgram(gav, repoIdent), packageName)
  }

  def buildPackageFor(jp: JavaProgram, packageName: String): JavaPackage = {
    val ident = jp.uid + "!" + packageName
    val jpa = new JavaPackage(packageName, ident, jp.repository)
    jpa.setParent(jp)
    jpa
  }

  def buildClass(gav: String, packageName: String, className: String, fqn: String, superTypeFqn: Option[String] = None, repoIdent: String = "mvn", hash: Array[Byte] = Array.empty): JavaClass = {
    buildClassFor(buildPackage(gav, packageName, repoIdent), className, fqn, superTypeFqn, hash)
  }

  def buildClassFor(jp: JavaPackage, className: String, fqn: String, superTypeFqn: Option[String] = None, hash: Array[Byte] = Array.empty): JavaClass = {
    val ident = jp.uid + "!" + fqn
    val classObj = new JavaClass(className, fqn, ident, superTypeFqn, jp.repository, hash)
    classObj.setParent(jp)
    classObj
  }

  def buildMethodFor(jc: JavaClass, methodName: String, returnTypeName: String, paramTypeNames: Seq[String]): JavaMethod = {
    val ident = jc.uid + "!" + buildMethodIdent(methodName, returnTypeName, paramTypeNames)
    val methodObj = new JavaMethod(methodName, returnTypeName, paramTypeNames, ident, jc.repository)
    methodObj.setParent(jc)
    methodObj
  }

  //TODO: Helper Functions for Method and Instruction

  abstract class PathIdentifiableJavaEntity private[entities] (entityName: String,
                                                     entityIdent: String,
                                                     entityUid: String,
                                                     repositoryIdent: String,
                                                     hashedBytes: Option[Array[Byte]]) extends SoftwareEntityData {
    override val name: String = entityName
    override val language: String = "java"
    override val repository: String = repositoryIdent

    override val binaryHash: Option[Array[Byte]] = hashedBytes

    override val uid: String = entityUid

    val identifier: String = entityIdent
  }

  class JavaLibrary(libraryName: String,
                    repositoryIdent: String) extends PathIdentifiableJavaEntity(libraryName, libraryName, libraryName, repositoryIdent, None){
    override val kind: SoftwareEntityKind = SoftwareEntityKind.Library
  }

  class JavaProgram(programName: String,
                    programIdent: String,
                    programUid: String,
                    repositoryIdent: String,
                    hashedBytes: Array[Byte]) extends PathIdentifiableJavaEntity(programName, programIdent, programUid, repositoryIdent, Some(hashedBytes)) {

    override val kind: SoftwareEntityKind = SoftwareEntityKind.Program

  }

  class JavaPackage(packageName: String,
                    packageUid: String,
                    repositoryIdent: String) extends PathIdentifiableJavaEntity(packageName, packageName, packageUid, repositoryIdent, None) {
    override val kind: SoftwareEntityKind = SoftwareEntityKind.Package
  }

  class JavaClass(className: String,
                  thisTypeFqn: String,
                  classUid: String,
                  superTypeFqn: Option[String],
                  repositoryIdent: String,
                  hashedBytes: Array[Byte]) extends PathIdentifiableJavaEntity(className, thisTypeFqn, classUid, repositoryIdent, Some(hashedBytes)){
    override val kind: SoftwareEntityKind = SoftwareEntityKind.Class

    val thisType: String = thisTypeFqn
    val superType: Option[String] = superTypeFqn
  }

  def buildMethodIdent(methodName: String, returnType: String, paramTypes: Seq[String]) =
    s"$returnType $methodName(${paramTypes.mkString(",")})"

  class JavaMethod(methodName: String,
                   returnTypeFqn: String,
                   paramTypeNames: Seq[String],
                   methodUid: String,
                   repositoryIdent: String) extends PathIdentifiableJavaEntity(methodName, buildMethodIdent(methodName, returnTypeFqn, paramTypeNames), methodUid, repositoryIdent, None){

    override val kind: SoftwareEntityKind = SoftwareEntityKind.Method

    val returnType: String = returnTypeFqn
    val paramCount: Int = paramTypeNames.size
    val paramTypes: Seq[String] = paramTypeNames
  }

  abstract class JavaStatement(name: String, pc: Int, stmtUid: String, repositoryIdent: String)
    extends PathIdentifiableJavaEntity(name, String.valueOf(pc), stmtUid, repositoryIdent, None){
    val instructionPc: Int = pc
  }

  class JavaInvokeStatement(methodName: String,
                            declaredTypeFqn: String,
                            paramCount: Int,
                            returnTypeFqn: String,
                            invocationType: JavaInvocationType,
                            pc: Int,
                            stmtUid: String,
                            repositoryIdent: String) extends JavaStatement(methodName, pc, stmtUid, repositoryIdent) {
    override val kind: SoftwareEntityKind = SoftwareEntityKind.InvocationStatement

    val targetMethodName: String = methodName
    val targetMethodParameterCount: Int = paramCount
    val returnTypeName: String = returnTypeFqn
    val targetTypeName: String = declaredTypeFqn
    val isStaticMethod: Boolean = invocationType == JavaInvocationType.Static
    val invokeStatementType: JavaInvocationType = invocationType
  }

  class JavaFieldAccessStatement(fieldName: String,
                                 fieldTypeFqn: String,
                                 declaredTypeFqn: String,
                                 accessType: JavaFieldAccessType,
                                 pc:Int,
                                 stmtUid: String,
                                 repositoryIdent: String) extends JavaStatement(fieldName, pc, stmtUid, repositoryIdent) {
    override val kind: SoftwareEntityKind = SoftwareEntityKind.FieldAccessStatement

    val targetFieldName: String = fieldName
    val targetFieldTypeName: String = fieldTypeFqn
    val targetTypeName: String = declaredTypeFqn
    val fieldAccessType: JavaFieldAccessType = accessType
  }

  object JavaInvocationType extends Enumeration {
    type JavaInvocationType = Value

    val Virtual: Value = Value(1)
    val Special: Value = Value(2)
    val Interface: Value = Value(3)
    val Static: Value = Value(4)
    val Dynamic: Value = Value(5)


    def fromId(id: Int): JavaInvocationType = id match {
      case 1 => Virtual
      case 2 => Special
      case 3 => Interface
      case 4 => Static
      case 5 => Dynamic
      case _ => throw new IllegalArgumentException(s"Invalid id for InvocationType $id")
    }
  }

  object JavaFieldAccessType extends Enumeration {
    type JavaFieldAccessType = Value

    val StaticPut: Value = Value(1)
    val StaticGet: Value = Value(2)
    val InstancePut: Value = Value(3)
    val InstanceGet: Value = Value(4)

    def fromId(id: Int): JavaFieldAccessType = id match {
      case 1 => StaticPut
      case 2 => StaticGet
      case 3 => InstancePut
      case 4 => InstanceGet
      case _ => throw new IllegalArgumentException(s"Invalid id for FieldAccessType $id")
    }
  }


}
