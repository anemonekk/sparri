package org.anon.spareuse.core.model.entities

import org.anon.spareuse.core.model.SoftwareEntityKind
import org.anon.spareuse.core.model.SoftwareEntityKind.SoftwareEntityKind
import org.anon.spareuse.core.model.entities.JavaEntities.JavaFieldAccessType.JavaFieldAccessType
import org.anon.spareuse.core.model.entities.JavaEntities.JavaInvocationType.JavaInvocationType
import org.anon.spareuse.core.model.SoftwareEntityKind
import org.opalj.br.MethodDescriptor
import org.opalj.tac.fpcf.analyses.cg.MethodDesc

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

  def buildClass(gav: String, packageName: String, className: String, fqn: String, isInterface:Boolean, isFinal:Boolean, isAbstract:Boolean, superTypeFqn: Option[String] = None, interfaceFqns: Set[String] = Set.empty, repoIdent: String = "mvn", hash: Array[Byte] = Array.empty): JavaClass = {
    buildClassFor(buildPackage(gav, packageName, repoIdent), className, fqn, isInterface, isFinal, isAbstract, superTypeFqn, interfaceFqns, hash)
  }

  def buildClassFor(jp: JavaPackage, className: String, fqn: String, isInterface: Boolean, isFinal: Boolean, isAbstract: Boolean, superTypeFqn: Option[String] = None, interfaceFqns: Set[String] = Set.empty, hash: Array[Byte] = Array.empty): JavaClass = {
    val ident = jp.uid + "!" + fqn
    val classObj = new JavaClass(className, fqn, ident, superTypeFqn, interfaceFqns, isInterface, isFinal, isAbstract, jp.repository, hash)
    classObj.setParent(jp)
    classObj
  }

  def buildMethodFor(jc: JavaClass, methodName: String, descriptor: String, isFinal: Boolean, isStatic: Boolean, isAbstract: Boolean, visibility: String, hashCode: Int): JavaMethod = {
    val ident = jc.uid + "!" + buildMethodIdent(methodName, descriptor)
    val methodObj = new JavaMethod(methodName, descriptor, ident, isFinal, isStatic, isAbstract, visibility, jc.repository, hashCode)
    methodObj.setParent(jc)
    methodObj
  }

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

  class JavaLibrary(val libraryName: String,
                    repositoryIdent: String) extends PathIdentifiableJavaEntity(libraryName, libraryName, libraryName, repositoryIdent, None){
    override val kind: SoftwareEntityKind = SoftwareEntityKind.Library

    def getPrograms: Set[JavaProgram] = getChildren.map(_.asInstanceOf[JavaProgram])
  }

  class JavaProgram(val programName: String,
                    val programIdent: String,
                    programUid: String,
                    repositoryIdent: String,
                    hashedBytes: Array[Byte]) extends PathIdentifiableJavaEntity(programName, programIdent, programUid, repositoryIdent, Some(hashedBytes)) {

    override val kind: SoftwareEntityKind = SoftwareEntityKind.Program

    private lazy val isGAV: Boolean = programName.count(_ == ':') == 2

    val ga: String = if(isGAV) programName.substring(0, programName.lastIndexOf(":")) else programName
    val v: String = if(isGAV) programName.substring(programName.lastIndexOf(":") + 1) else programName

    def getPackages: Set[JavaPackage] = getChildren.map(_.asInstanceOf[JavaPackage])

    def allClasses: Set[JavaClass] = getPackages.flatMap(_.getClasses)

    def allMethods: Set[JavaMethod] = allClasses.flatMap(_.getMethods)

  }

  class JavaPackage(packageName: String,
                    packageUid: String,
                    repositoryIdent: String) extends PathIdentifiableJavaEntity(packageName, packageName, packageUid, repositoryIdent, None) {
    override val kind: SoftwareEntityKind = SoftwareEntityKind.Package

    def getClasses: Set[JavaClass] = getChildren.map(_.asInstanceOf[JavaClass])

    def allMethods: Set[JavaMethod] = getClasses.flatMap(_.getMethods)
  }

  class JavaClass(className: String,
                  thisTypeFqn: String,
                  classUid: String,
                  superTypeFqn: Option[String],
                  interfaceFqns: Set[String],
                  interfaceType: Boolean,
                  finalType: Boolean,
                  abstractType: Boolean,
                  repositoryIdent: String,
                  hashedBytes: Array[Byte]) extends PathIdentifiableJavaEntity(className, thisTypeFqn, classUid, repositoryIdent, Some(hashedBytes)){
    override val kind: SoftwareEntityKind = SoftwareEntityKind.Class

    val thisType: String = thisTypeFqn
    val superType: Option[String] = superTypeFqn
    val interfaceTypes: Set[String]= interfaceFqns
    val isInterface: Boolean = interfaceType
    val isFinal: Boolean = finalType
    val isAbstract: Boolean = abstractType

    def getMethods: Set[JavaMethod] = getChildren.map(_.asInstanceOf[JavaMethod])
  }

  def buildMethodIdent(methodName: String, jvmDescriptor: String) = s"$methodName: $jvmDescriptor"

  class JavaMethod(methodName: String,
                   jvmDescriptor: String,
                   methodUid: String,
                   finalMethod: Boolean,
                   staticMethod: Boolean,
                   abstractMethod: Boolean,
                   methodVisibility: String,
                   repositoryIdent: String,
                   hash: Int) extends PathIdentifiableJavaEntity(methodName, buildMethodIdent(methodName, jvmDescriptor), methodUid, repositoryIdent, None){

    override val kind: SoftwareEntityKind = SoftwareEntityKind.Method

    private lazy val opalDescriptor = MethodDescriptor(jvmDescriptor)

    val descriptor: String = jvmDescriptor
    val isFinal: Boolean = finalMethod
    val isStatic: Boolean = staticMethod
    val isAbstract: Boolean = abstractMethod
    val visibility: String = methodVisibility
    val methodHash: Int = hash

    def paramTypes: Seq[String] = opalDescriptor.parameterTypes.map(_.toJVMTypeName)
    def returnType: String = opalDescriptor.returnType.toJVMTypeName


    def getEnclosingClass: Option[JavaClass] = getParent.map(_.asInstanceOf[JavaClass])
    def getStatements: Seq[JavaStatement] = getChildren.map(_.asInstanceOf[JavaStatement]).toSeq.sortBy(_.instructionPc)
    def getNewStatements: Seq[JavaNewInstanceStatement] = getChildren.collect{ case x: JavaNewInstanceStatement => x }.toSeq.sortBy(_.instructionPc)
    def getInvocationStatements: Seq[JavaInvokeStatement] = getChildren.collect{ case x: JavaInvokeStatement => x }.toSeq.sortBy(_.instructionPc)
    def getFieldAccessStatements: Seq[JavaFieldAccessStatement] = getChildren.collect{ case x: JavaFieldAccessStatement => x }.toSeq.sortBy(_.instructionPc)
  }

  abstract class JavaStatement(name: String, pc: Int, stmtUid: String, repositoryIdent: String)
    extends PathIdentifiableJavaEntity(name, String.valueOf(pc), stmtUid, repositoryIdent, None){
    val instructionPc: Int = pc
  }

  class JavaInvokeStatement(methodName: String,
                            declaredTypeFqn: String,
                            jvmDescriptor: String,
                            invocationType: JavaInvocationType,
                            pc: Int,
                            stmtUid: String,
                            repositoryIdent: String) extends JavaStatement(methodName, pc, stmtUid, repositoryIdent) {
    override val kind: SoftwareEntityKind = SoftwareEntityKind.InvocationStatement

    val targetMethodName: String = methodName
    val targetDescriptor: String = jvmDescriptor
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

  class JavaNewInstanceStatement(typeName: String, pc: Int, stmtUid: String, repositoryIdent: String)
    extends JavaStatement(typeName, pc, stmtUid, repositoryIdent){
    override val kind: SoftwareEntityKind = SoftwareEntityKind.NewInstanceStatement
    val instantiatedTypeName: String = typeName
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
