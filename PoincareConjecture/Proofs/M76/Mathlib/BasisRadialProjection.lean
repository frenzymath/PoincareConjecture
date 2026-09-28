import PoincareConjecture.Proofs.M76.Mathlib.BasisEvaluation
import PoincareConjecture.Proofs.M76.Mathlib.FixedRadialNormalization











set_option autoImplicit false

open Set

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




abbrev BasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  {Q : E →L[ℝ] F // A.IsRadialEmbedding (fun i => Q (b i))}




noncomputable def basisRadialProjectionHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    A.BasisRadialProjection b F ≃ₜ A.RadialEmbedding F :=
  b.evaluationContinuousLinearEquiv.toHomeomorph.subtype (fun Q => by
    change A.IsRadialEmbedding (fun i => Q (b i)) ↔
      A.IsRadialEmbedding (b.evaluationContinuousLinearEquiv Q)
    have he : b.evaluationContinuousLinearEquiv Q = fun i => Q (b i) :=
      funext (b.evaluationContinuousLinearEquiv_apply Q)
    rw [he])



abbrev FixedBasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (s : Set ι) (w : ι → F) :=
  {Q : A.BasisRadialProjection b F // EqOn (fun i => Q.val (b i)) w s}




noncomputable def fixedBasisRadialProjectionHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (s : Set ι) (w : ι → F) :
    A.FixedBasisRadialProjection b s w ≃ₜ A.FixedRadialEmbedding s w :=
  (basisRadialProjectionHomeomorph A b F).subtype (fun Q => by
    change EqOn (fun i => Q.val (b i)) w s ↔
      EqOn (b.evaluationContinuousLinearEquiv Q.val) w s
    have he : b.evaluationContinuousLinearEquiv Q.val = fun i => Q.val (b i) :=
      funext (b.evaluationContinuousLinearEquiv_apply Q.val)
    rw [he])

end AbstractSimplicialComplex
