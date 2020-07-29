/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.analysis.cfa

import org.jetbrains.kotlin.fir.FirSession
import org.jetbrains.kotlin.fir.analysis.checkers.cfa.FirControlFlowChecker
import org.jetbrains.kotlin.fir.analysis.diagnostics.DiagnosticReporter
import org.jetbrains.kotlin.fir.analysis.diagnostics.FirErrors
import org.jetbrains.kotlin.fir.contracts.FirResolvedContractDescription
import org.jetbrains.kotlin.fir.contracts.description.*
import org.jetbrains.kotlin.fir.declarations.FirContractDescriptionOwner
import org.jetbrains.kotlin.fir.declarations.FirFunction
import org.jetbrains.kotlin.fir.expressions.*
import org.jetbrains.kotlin.fir.resolve.dfa.*
import org.jetbrains.kotlin.fir.resolve.dfa.cfg.CFGNode
import org.jetbrains.kotlin.fir.resolve.dfa.cfg.ControlFlowGraph
import org.jetbrains.kotlin.fir.resolve.dfa.cfg.JumpNode
import org.jetbrains.kotlin.fir.symbols.AbstractFirBasedSymbol
import org.jetbrains.kotlin.fir.typeContext
import org.jetbrains.kotlin.fir.types.ConeKotlinType
import org.jetbrains.kotlin.fir.types.ConeTypeIntersector
import org.jetbrains.kotlin.fir.types.coneType
import org.jetbrains.kotlin.fir.types.isNullable
import org.jetbrains.kotlin.types.AbstractTypeChecker
import org.jetbrains.kotlin.types.model.KotlinTypeMarker
import org.jetbrains.kotlin.utils.addIfNotNull

object FirReturnsImpliesAnalyzer : FirControlFlowChecker() {

    override fun analyze(graph: ControlFlowGraph, reporter: DiagnosticReporter) {
        val function = graph.declaration as? FirFunction<*> ?: return
        val graphRef = function.controlFlowGraphReference as FirControlFlowGraphReferenceImpl
        val variableStorage = graphRef.variableStorage
        if (function !is FirContractDescriptionOwner || variableStorage == null) return

        val effects = (function.contractDescription as? FirResolvedContractDescription)?.effects
            ?.filterIsInstance<ConeConditionalEffectDeclaration>()
            ?.filter { it.effect is ConeReturnsEffectDeclaration }

        if (effects.isNullOrEmpty()) return

        val logicSystem = object : PersistentLogicSystem(function.session.typeContext) {
            override fun processUpdatedReceiverVariable(flow: PersistentFlow, variable: RealVariable) =
                throw IllegalStateException("Receiver variable update is not possible for this logic system")

            override fun updateAllReceivers(flow: PersistentFlow) =
                throw IllegalStateException("Update of all receivers is not possible for this logic system")
        }

        val builtinTypes = function.session.builtinTypes
        val typeContext = function.session.typeContext

        fun KotlinTypeMarker.isSupertypeOf(type: KotlinTypeMarker?) =
            type != null && AbstractTypeChecker.isSubtypeOf(typeContext, type, this)

        fun Collection<ConeKotlinType>.intersectTypes(): ConeKotlinType? =
            if (isNotEmpty()) ConeTypeIntersector.intersectTypes(typeContext, this.toList()) else null

        effects.forEach { effectDeclaration ->
            val effect = effectDeclaration.effect as ConeReturnsEffectDeclaration
            val condition = effectDeclaration.condition

            // returns true if wrong condition at node
            fun checkNode(node: CFGNode<*>): Boolean {
                val flow = graphRef.flowOnNodes.getValue(node) as PersistentFlow

                val isReturn = node is JumpNode && node.fir is FirReturnExpression
                val resultExpression = if (isReturn) (node.fir as FirReturnExpression).result else node.fir

                val expressionType = (resultExpression as? FirExpression)?.typeRef?.coneType
                if (expressionType == builtinTypes.nothingType.type) return false

                if (isReturn && resultExpression is FirWhenExpression) {
                    return node.previousNodes(4).any { checkNode(it) } // When exit -> When branch exit -> Block exit -> Last expression
                }

                var typeStatements: TypeStatements = flow.approvedTypeStatements
                val implications = flow.logicStatements.flatMap { it.value }

                if (effect.value != ConeConstantReference.WILDCARD) {
                    val operation = effect.value.toOperation()
                    if (expressionType != null && expressionType.isInapplicableWith(operation, function.session)) return false

                    if (resultExpression is FirConstExpression<*>) {
                        if (!resultExpression.isApplicableWith(operation)) return false
                    } else {
                        val resultVar = variableStorage.getOrCreateVariable(flow, resultExpression)
                        val newTypeStatements: MutableTypeStatements = mutableMapOf()

                        logicSystem.approveStatementsTo(
                            newTypeStatements,
                            flow,
                            OperationStatement(resultVar, operation),
                            implications
                        )
                        newTypeStatements.mergeTypeStatements(flow.approvedTypeStatements)

                        if (resultVar.isReal()) {
                            if (operation == Operation.NotEqNull) {
                                newTypeStatements.addStatement(resultVar, simpleTypeStatement(resultVar, true, builtinTypes.anyType.type))
                            } else if (operation == Operation.EqNull) {
                                newTypeStatements.addStatement(resultVar, simpleTypeStatement(resultVar, false, builtinTypes.anyType.type))
                            }
                        }

                        typeStatements = newTypeStatements
                    }
                }

                val conditionStatements = condition.buildTypeStatements(function, logicSystem, variableStorage, flow) ?: return false

                for ((realVar, requiredTypeStatement) in conditionStatements) {
                    val fixedRealVar = typeStatements.keys.find { it.identifier == realVar.identifier } ?: realVar
                    val resultTypeStatement = typeStatements[fixedRealVar]

                    val resultType = mutableListOf<ConeKotlinType>().apply {
                        addIfNotNull(function.getParameterType(fixedRealVar.identifier.symbol))
                        if (resultTypeStatement != null) addAll(resultTypeStatement.exactType)
                    }.intersectTypes()

                    val requiredType = requiredTypeStatement.exactType.intersectTypes()
                    if (requiredType != null && !requiredType.isSupertypeOf(resultType)) return true
                }
                return false
            }

            val wrongCondition = graph.exitNode.previousCfgNodes.any { checkNode(it) }
            if (wrongCondition) {
                function.contractDescription.source?.let {
                    reporter.report(FirErrors.WRONG_IMPLIES_CONDITION.on(it))
                }
            }
        }
    }

    private fun CFGNode<*>.previousNodes(depth: Int, nodes: MutableList<CFGNode<*>> = mutableListOf()): List<CFGNode<*>> {
        if (depth == 0) nodes.add(this) else previousCfgNodes.forEach { it.previousNodes(depth - 1, nodes) }
        return nodes
    }

    private fun FirFunction<*>.getParameterType(symbol: AbstractFirBasedSymbol<*>): ConeKotlinType? {
        return (if (this.symbol == symbol) receiverTypeRef else valueParameters.find { it.symbol == symbol }?.returnTypeRef)?.coneType
    }

    private fun FirFunction<*>.getParameterSymbol(index: Int): AbstractFirBasedSymbol<*> {
        return if (index == -1) this.symbol else this.valueParameters[index].symbol
    }

    private fun ConeKotlinType.isInapplicableWith(operation: Operation, session: FirSession): Boolean {
        return (operation == Operation.EqFalse || operation == Operation.EqTrue)
                && !AbstractTypeChecker.isSubtypeOf(session.typeContext, session.builtinTypes.booleanType.type, this)
                || operation == Operation.EqNull && !isNullable
    }

    private fun FirConstExpression<*>.isApplicableWith(operation: Operation): Boolean = when {
        kind == FirConstKind.Null -> operation == Operation.EqNull
        kind == FirConstKind.Boolean && operation == Operation.EqTrue -> (value as Boolean)
        kind == FirConstKind.Boolean && operation == Operation.EqFalse -> !(value as Boolean)
        else -> true
    }

    private fun ConeBooleanExpression.buildTypeStatements(
        function: FirFunction<*>,
        logicSystem: LogicSystem<*>,
        variableStorage: VariableStorage,
        flow: Flow
    ): MutableTypeStatements? = when (this) {
        is ConeBinaryLogicExpression -> {
            val left = left.buildTypeStatements(function, logicSystem, variableStorage, flow)
            val right = right.buildTypeStatements(function, logicSystem, variableStorage, flow)
            if (left != null && right != null) {
                if (kind == LogicOperationKind.AND) {
                    left.apply { mergeTypeStatements(right) }
                } else logicSystem.orForTypeStatements(left, right)
            } else (left ?: right)
        }
        is ConeIsInstancePredicate -> {
            val fir = function.getParameterSymbol(arg.parameterIndex).fir
            val realVar = variableStorage.getOrCreateRealVariable(flow, fir.symbol, fir)
            realVar?.to(simpleTypeStatement(realVar, !isNegated, type))?.let { mutableMapOf(it) }
        }
        is ConeIsNullPredicate -> {
            val fir = function.getParameterSymbol(arg.parameterIndex).fir
            val realVar = variableStorage.getOrCreateRealVariable(flow, fir.symbol, fir)
            realVar?.to(simpleTypeStatement(realVar, isNegated, function.session.builtinTypes.anyType.type))?.let { mutableMapOf(it) }
        }
        is ConeLogicalNot -> arg.buildTypeStatements(function, logicSystem, variableStorage, flow)
            ?.mapValuesTo(mutableMapOf()) { (_, value) -> value.invert() }

        else -> null
    }

    private fun simpleTypeStatement(realVar: RealVariable, exactType: Boolean, type: ConeKotlinType): MutableTypeStatement {
        return MutableTypeStatement(
            realVar,
            if (exactType) linkedSetOf(type) else linkedSetOf(),
            if (!exactType) linkedSetOf(type) else linkedSetOf()
        )
    }
}