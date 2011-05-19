package scala.virtualization.lms
package epfl
package test7

import common._
import original._
import original.Conversions._

import java.io.{Writer, PrintWriter}
import collection.immutable.HashMap


trait MDArrayTypingBubbleUp extends MDArrayTypingWithScope {

  import IR.{Sym, Exp, Def, TP, findDefinition}
  var remainingConstraints: List[TypingConstraint] = Nil
  var scopeSubsts: SubstitutionList = new SubstitutionList(Nil)

  var runtimeChecks: Map[Sym[_], List[TypingConstraint]] = Map.empty

  def fillInRuntimeChecks(sym: Sym[_]): Unit = findDefinition(sym) match {
    case None =>
      runtimeChecks = runtimeChecks + (sym -> Nil)
    case Some(tp) =>
      val rhs: Def[_] = tp.rhs
      val argSyms = syms(rhs)
      var checks: List[TypingConstraint] = Nil

      // add the runtime checks for prerequisites
      checks = getConstraints(sym, rhs).filter(_.prereq)

      // add the runtime checks for bubbling up
      for (argSym <- argSyms) {
        if (scopeSubsts(ShapeVar(argSym)) != currentScope.fullSubsts(ShapeVar(argSym)))
          checks = Equality(scopeSubsts(ShapeVar(argSym)), currentScope.fullSubsts(ShapeVar(argSym)), postReq, "Bubble up shape for " + argSym.toString + " <- " + rhs.toString) :: checks

        if (scopeSubsts(ValueVar(argSym)) != currentScope.fullSubsts(ValueVar(argSym)))
          checks = Equality(scopeSubsts(ValueVar(argSym)), currentScope.fullSubsts(ValueVar(argSym)), postReq, "Bubble up value for " + argSym.toString + " <- " + rhs.toString) :: checks
      }

      runtimeChecks = runtimeChecks + (sym -> checks)
      for (argSym <- argSyms)
        fillInRuntimeChecks(argSym)
  }

  override def doTyping(result: Exp[_], debug: Boolean = false): Unit = {
    // Let the bottom layers do their work
    super.doTyping(result, debug)

    // Create runtimeChecks
    fillInRuntimeChecks(result.asInstanceOf[Sym[_]])
  }

  // Generate only bubble up constraints, for the runtime constraints we need to
  def getBubbleUpConstraints(sym: Sym[_], rhs: Def[_]): List[TypingConstraint] = {

    var nodeConstraints: List[TypingConstraint] = Nil

    // 1. ensure bubbling up
    for (sym <- syms(rhs)) {
      if (scopeSubsts(ShapeVar(sym)) != currentScope.fullSubsts(ShapeVar(sym))) {
        val shapeConstraint = Equality(scopeSubsts(ShapeVar(sym)), currentScope.fullSubsts(ShapeVar(sym)), postReq, "Bubble up for " + sym.toString + " <- " + rhs.toString)
        nodeConstraints = shapeConstraint::nodeConstraints
        assumeConstraint(shapeConstraint)
      }

      if (scopeSubsts(ValueVar(sym)) != currentScope.fullSubsts(ValueVar(sym))) {
        val valueConstraint = Equality(scopeSubsts(ValueVar(sym)), currentScope.fullSubsts(ValueVar(sym)), postReq, "Bubble up for " + sym.toString + " <- " + rhs.toString)
        nodeConstraints = valueConstraint::nodeConstraints
        assumeConstraint(valueConstraint)
      }
    }

    // 2. assume the postconditions
    val constraints = getConstraints(sym, rhs).filterNot(_.prereq)
    for (constraint <- constraints)
      assumeConstraint(constraint)

    nodeConstraints
  }

  // Generate/check runtime prereqs
  def getRuntimeChecks(sym: Sym[_], rhs: Def[_]): List[TypingConstraint] =
    Nil


  protected def assumeConstraint(constraint: TypingConstraint): Unit = {

    remainingConstraints = scopeSubsts(constraint) :: remainingConstraints
    eliminateConstraints()
  }


  protected def eliminateConstraints(): Unit = {

    val (substitutions, constraints) = computeSubstitutions(remainingConstraints, false)
    remainingConstraints = constraints
    scopeSubsts = new SubstitutionList(scopeSubsts.substList ::: substitutions.substList)
  }


  def withinDifferentScopes(ifSym: Sym[_], pairs: List[Pair[Sym[_], ()=>Unit]]): Unit = {

    var scopes: List[TypingScope] = Nil
    var parentScopeSubsts = scopeSubsts
    var parentRemainingConstraints = remainingConstraints
    var scopeSubstsList: List[SubstitutionList] = Nil

    // prepare scopes for each action
    for (pair <- pairs) {
      val (sym, action) = pair
      val oldScope = currentScope

      if (HAVE_SCOPES) {
        // find the new scope
        val newScopes = currentScope.children.filter(scope => (scope.sym == sym) && (scope.ifSym == ifSym))
        if (newScopes.length < 1) sys.error("There is no scope for the sym. CurrentSym: " + currentScope.sym + " NewSym: " + sym + " Available: " + currentScope.children.map(_.sym).mkString(" "))
        val newScope = newScopes.head

        scopes = newScope :: scopes
        // set everything up for the new scope
        currentScope = newScope
      }

      // emit the code
      action()

      if (HAVE_SCOPES) {
        // recover the scope state
        scopeSubstsList = scopeSubsts :: scopeSubstsList
        scopeSubsts = parentScopeSubsts
        remainingConstraints = parentRemainingConstraints
        currentScope = oldScope
      }
    }

    // if we have scopes, we have to reconcile the scope substitutions and join them into the parent scope
    // if we don't have scoeps, the constraints have been added and eliminated along the way :)
    if (HAVE_SCOPES) {
      // reconcile scopes
      remainingConstraints = remainingConstraints ::: scopeSubsts(reconcile(scopeSubstsList))
      eliminateConstraints()
    }
  }
}