import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialGramPath
import PoincareConjecture.Proofs.M14.Sec6_7_TangentialDerivative
import PoincareConjecture.Proofs.M14.Sec6_7_StableDensity

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

noncomputable def exponentialWeightedJacobian (E : M14ExponentialFamily G T x)
    (v : Fin n → G.Horizontal x) (Z : G.Horizontal x) (s : ℝ) : ℝ :=
  Real.rpow s (-(n : ℝ)) * Real.exp (-E.reduced_length Z s) * exponentialJacobian E v Z s

theorem exponentialWeightedJacobian_nonneg (E : M14ExponentialFamily G T x)
    (v : Fin n → G.Horizontal x) (Z : G.Horizontal x) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ exponentialWeightedJacobian E v Z s :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_pos _).le)
    (exponentialJacobian_nonneg E v Z s)

theorem exponential_reducedLength_continuousOn_prefix
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) :
    ContinuousOn (E.reduced_length Z) (Ioc 0 b) := by
  have hsub : Ioc 0 b ⊆ {r | (Z, r) ∈ E.domain} := fun r hr =>
    (E.maximal_lifetime Z).out (E.domain_zero Z) hb ⟨hr.1.le, hr.2⟩
  intro s hs
  exact (exponential_reducedLength_hasDerivWithinAt hM12 E (hsub hs) hs.1).continuousWithinAt.mono
    hsub

theorem exponentialWeightedJacobian_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Fin n → G.Horizontal x)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    ContinuousOn (exponentialWeightedJacobian E v Z) (Ioc 0 b) := by
  have hp : ContinuousOn (fun s : ℝ => Real.rpow s (-(n : ℝ))) (Ioc 0 b) :=
    fun s hs => (Real.hasDerivAt_rpow_const (p := -(n : ℝ))
      (Or.inl hs.1.ne')).continuousAt.continuousWithinAt
  exact (hp.mul (Real.continuous_exp.comp_continuousOn
    (exponential_reducedLength_continuousOn_prefix hM12 E hb).neg)).mul
      ((exponentialJacobian_continuousOn hM04 hM12 E v hb hpos).mono Ioc_subset_Icc_self)

theorem stableDensity_mul_jacobian_eq_weighted {τ : ℝ}
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    (D : M14MeasureJacobianData G T τ x E H) {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    stableReducedVolumeDensity H (H.endpoint_slice_map Z) * D.jacobian Z =
      exponentialWeightedJacobian E D.sourceBasis Z (Real.sqrt τ) := by
  have hl : M14ReducedLengthValue G T 0 τ x (H.endpoint_slice_map Z).val =
      E.reduced_length Z (Real.sqrt τ) :=
    (reducedLengthValue_stableEndpoint_eq_action H hZ).trans
      (E.reduced_length_eq Z (Real.sqrt τ) (H.survivor Z hZ)
        (Real.sqrt_pos.mpr H.tau_pos)).symm
  have hpower : Real.rpow (Real.sqrt τ) (-(n : ℝ)) = Real.rpow τ (-(n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    change (τ ^ (1 / 2 : ℝ)) ^ (-(n : ℝ)) = τ ^ (-(n : ℝ) / 2)
    rw [← Real.rpow_mul H.tau_pos.le]
    congr 1
    ring
  rw [stableReducedVolumeDensity_eq H ⟨Z, hZ, rfl⟩, hl,
    measureJacobian_eq_exponentialJacobian E H D hZ]
  simp only [exponentialWeightedJacobian, hpower]

end PoincareConjecture.M14
