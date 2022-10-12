package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.utils.Library
import lisa.utils.tactics.ProofStepLib.*
import lisa.utils.Parser.{parseFormula, parseSequent, parseTerm}
import lisa.kernel.fol.FOL.*

trait ProofsHelpers {
    library: Library & WithProofs =>
    given Library = library
    export BasicStepTactic.*
    export SimpleDeducedSteps.*
    private def proof: Proof = proofStack.head


    case class HaveSequent private[ProofsHelpers](bot:Sequent) {
        infix def by(just: ProofStepWithoutBot)(using String => Unit)(using finishOutput: Throwable => Nothing) : library.Proof#DoubleStep = {
            val r = just.asProofStep(bot)
            r.validate(library)
        }
    }

    case class AndThenSequent private[ProofsHelpers](bot:Sequent) {
        infix def by[N <: Int & Singleton](just: ProofStepWithoutBotNorPrem[N])(using String => Unit)(using finishOutput: Throwable => Nothing) : library.Proof#DoubleStep = {
            val r = just.asProofStepWithoutBot(Seq(proof.mostRecentStep._2)).asProofStep(bot)
            r.validate(library)
        }
    }

    /**
     * Claim the given Sequent as a ProofStep, which may require a justification by a proof tactic and premises.
     */
    def have(res:Sequent): HaveSequent = HaveSequent(res)
    /**
     * Claim the given Sequent as a ProofStep, which may require a justification by a proof tactic and premises.
     */
    def have(res:String): HaveSequent = HaveSequent(parseSequent(res))
    def have(instJust: InstantiatedJustification)(using String => Unit)(using finishOutput: Throwable => Nothing): library.Proof#DoubleStep = {
        val just = instJust.just
        val (seq, ref) = proof.getSequentAndInt(just)
        if (instJust.instsPred.isEmpty && instJust.instsTerm.isEmpty && instJust.instForall.isEmpty){
            have(seq) by Trivial(ref)
        } else if (instJust.instsPred.isEmpty && instJust.instForall.isEmpty){
            val res = (seq.left.map(phi => instantiateTermSchemas(phi, instJust.instsTerm)) |- seq.right.map(phi => instantiateTermSchemas(phi, instJust.instsTerm)))
            have(res) by InstFunSchema(instJust.instsTerm)(ref)
        } else if (instJust.instsTerm.isEmpty && instJust.instForall.isEmpty){
            val res = (seq.left.map(phi => instantiatePredicateSchemas(phi, instJust.instsPred)) |- seq.right.map(phi => instantiatePredicateSchemas(phi, instJust.instsPred)))
            have(res) by InstPredSchema(instJust.instsPred)(ref)
        } else if(instJust.instsPred.isEmpty && instJust.instsTerm.isEmpty){
            ???
        } else {
            ???
        }
    }

    /**
     * Claim the given Sequent as a ProofStep directly following the previously proven tactic,
     * which may require a justification by a proof tactic.
     */
    def andThen(res:Sequent): AndThenSequent = AndThenSequent(res)
    /**
     * Claim the given Sequent as a ProofStep directly following the previously proven tactic,
     * which may require a justification by a proof tactic.
     */
    def andThen(res:String): AndThenSequent = AndThenSequent(parseSequent(res))

    /**
     * Import the given justification (Axiom, Theorem or Definition) into the current proof.
     */
    def withImport(just:theory.Justification):library.Proof#ImportedFact = {
        proofStack.head.newJustifiedImport(just)

    }

    /**
     * Assume the given formula in all future left hand-side of claimed sequents.
     */
    def assume(f:Formula):Formula = {
        proofStack.head.addAssumption(f)
        f
    }
    def assume(just:theory.Justification):Formula = {
        assume(cjij(just))
    }

    def assume(instJust: InstantiatedJustification):Formula = {
        val just = instJust.just
        val (seq, ref) = proof.getSequentAndInt(just)
        val f = (seq.left.map(phi => instantiatePredicateSchemas(phi, instJust.instsPred)) |- seq.right.map(phi => instantiatePredicateSchemas(phi, instJust.instsPred)))
        assume(f.right.head)
    }

    /**
     * Store the given import and use it to discharge the proof of one of its assumption at the very end.
     */
    def endDischarge(ji: Library#Proof#ImportedFact):Unit = {
        val p: Proof = proof
        if (p.validInThisProof(ji)){
            val p = proof
            p.addDischarge(ji.asInstanceOf[p.ImportedFact])
        }
    }


    given Conversion[ProofStepWithoutBotNorPrem[0], ProofStepWithoutBot] = _.asProofStepWithoutBot(Seq())


    case class InstantiatedJustification(just:theory.Justification, instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula], instsTerm: Map[SchematicTermLabel, LambdaTermTerm], instForall:Seq[Term])


    extension (just: theory.Justification) {/*
        def apply(insts: ((SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term)*): InstantiatedJustification = {
            val instsPred: Map[SchematicVarOrPredLabel, LambdaTermFormula] = insts.filter(isLTT).asInstanceOf[Seq[(SchematicVarOrPredLabel, LambdaTermFormula)]].toMap
            val instsTerm: Map[SchematicTermLabel, LambdaTermTerm] = insts.filter(isLTF).asInstanceOf[Seq[(SchematicTermLabel, LambdaTermTerm)]].toMap
            val instsForall: Seq[Term] = insts.filter(isTerm).asInstanceOf[Seq[Term]]
        InstantiatedJustification(just, instsPred, instsTerm, instsForall)
        }*/

        def apply(insts: (VariableLabel, Term)*): InstantiatedJustification = {
            InstantiatedJustification(just, Map(), insts.map((x:VariableLabel, t:Term) => (x, LambdaTermTerm(Seq(), t))).toMap, Seq())
        }
    }

    private def isTerm(x: (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term):Boolean = x.isInstanceOf[Term]
    private def isLTT(x: (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term):Boolean = x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaTermTerm]
    private def isLTF(x: (SchematicVarOrPredLabel, LambdaTermFormula) | (SchematicTermLabel, LambdaTermTerm) | Term):Boolean = x.isInstanceOf[Tuple2[_, _]] && x.asInstanceOf[Tuple2[_, _]]._2.isInstanceOf[LambdaTermFormula]
    given cjij: Conversion[theory.Justification, InstantiatedJustification] = InstantiatedJustification(_, Map.empty, Map.empty, Seq())

}
