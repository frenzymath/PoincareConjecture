import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.BasisEvaluation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FixedRadialNormalization

/-!
# Radial realizations in ambient linear-map coordinates

When the source vertices form a basis of their span, their radial
realizations correspond homeomorphically to ambient linear maps with
the same column data. Prescribed vertex values are retained. This is
the coordinate part of Cairns 1940, Lemma 5.1, p. 801, preceding the
comparison with transverse kernels; see M76 derivation 25.
-/

set_option autoImplicit false

open Set

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ambient linear maps whose basis images form a faithful radial
realization. This is a coordinate model, prior to the transverse-kernel
comparison. See Cairns p. 801 and M76 derivation 25. -/
abbrev BasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  {Q : E →L[ℝ] F // A.IsRadialEmbedding (fun i => Q (b i))}

/-- Evaluation on the source vertex basis identifies the linear-map
model with the actual radial vertex space.
See Cairns p. 801 and M76 derivation 25. -/
noncomputable def basisRadialProjectionHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    A.BasisRadialProjection b F ≃ₜ A.RadialEmbedding F :=
  b.evaluationContinuousLinearEquiv.toHomeomorph.subtype (fun Q => by
    change A.IsRadialEmbedding (fun i => Q (b i)) ↔
      A.IsRadialEmbedding (b.evaluationContinuousLinearEquiv Q)
    have he : b.evaluationContinuousLinearEquiv Q = fun i => Q (b i) :=
      funext (b.evaluationContinuousLinearEquiv_apply Q)
    rw [he])

/-- The linear-map model with selected column values fixed.
See Cairns p. 801 and M76 derivation 25. -/
abbrev FixedBasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (s : Set ι) (w : ι → F) :=
  {Q : A.BasisRadialProjection b F // EqOn (fun i => Q.val (b i)) w s}

/-- Fixed source-basis columns correspond exactly to fixed vertex
coordinates, with both subspace topologies unchanged.
See Cairns p. 801 and M76 derivation 25. -/
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
