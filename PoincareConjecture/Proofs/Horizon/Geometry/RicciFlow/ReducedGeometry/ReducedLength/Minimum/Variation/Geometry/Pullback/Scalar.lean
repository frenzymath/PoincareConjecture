import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Congruence







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def smulParametricExtension {C : Set ℝ} {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn C α Y) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ParametricAlongCurveExtensionOn C α (fun s ↦ f s • Y s) where
  extension := fun s y ↦ f s • E.extension s y
  domain := E.domain
  open_domain := E.open_domain
  graph_mem := E.graph_mem
  smooth z hz := (parametricExtension_contMDiffAt_smul_reparam E (f := id)
    hz contDiffAt_id hf.contDiffAt).contMDiffWithinAt
  agrees s hs := by rw [E.agrees s hs]

theorem pullbackCovariantDerivative_smul {J C : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn C α Y)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (H : ParametricAlongCurveExtensionOn C α (fun s ↦ f s • Y s))
    {s : ℝ} (hs : s ∈ C) (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α (fun r ↦ f r • Y r) C H s =
      deriv f s • Y s + f s • pullbackCovariantDerivative F time α Y C E s := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  rw [pullbackCovariantDerivative_extension_independent F time H
    (smulParametricExtension E f hf) hs hC hα]
  have hd := ((hf.differentiable (by simp)) s).hasDerivAt.smul
    (parametricExtension_differentiableAt_time E (E.graph_mem s hs)).hasDerivAt
  change HasDerivAt (fun r ↦ f r • E.extension r (α s))
    (f s • deriv (fun r ↦ E.extension r (α s)) s + deriv f s • E.extension s (α s)) s at hd
  have hc := (F.connection (time s)).connection.isCovariantDerivativeOnUniv.smul_const (f s)
    ((parametricExtension_contMDiffAt_space E (E.graph_mem s hs)).mdifferentiableAt (by simp))
  simp only [pullbackCovariantDerivative, smulParametricExtension]
  rw [hd.deriv]
  change f s • deriv (fun r ↦ E.extension r (α s)) s + deriv f s • E.extension s (α s) +
      ((F.connection (time s)).connection (f s • E.extension s) (α s))
        (curveVelocityWithin α C s) = _
  rw [hc, E.agrees s hs]
  simp only [ContinuousLinearMap.smul_apply, smul_add]
  abel

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
