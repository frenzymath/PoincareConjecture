import PoincareConjecture.Proofs.M14.Sec6_2_VariationVelocity
import PoincareConjecture.Proofs.M08.VariationIntegral
import PoincareConjecture.Statements.M12GeneralizedEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}



noncomputable def variationActionDensity (V : M14LVariationData G p R) (z : ℝ × ℝ) : ℝ :=
  2 * z.1 ^ 2 * horizontalScalarCurvature G.leafwise (V.squareFamily z.1 z.2) +
    (1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (V.squareFamily z.1 z.2)
      (variationSquareVelocity V z.1 z.2) (variationSquareVelocity V z.1 z.2)

private theorem parameterDomain_isOpen (V : M14LVariationData G p R) :
    IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo

set_option maxHeartbeats 1000000 in



theorem variationActionDensity_contDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) :
    ContDiffOn ℝ ∞ (variationActionDensity V)
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain) := by
  let S := M14SqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain
  let α := fun z : ℝ × ℝ => V.squareFamily z.1 z.2
  have hα : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (spacetimeModel n) ∞ α S := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact V.square_smooth.mono V.square_contains
  have hA : ContMDiffOn (𝓘(ℝ, ℝ × ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × ℝ => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (α z) (variationSquareVelocity V z.1 z.2)) S := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact variationSquareVelocity_smooth V
  have hmetric := G.spacetime.horizontalMetric.contMDiff.comp_contMDiffOn hα
  have hpair := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ) hA hA
  have hg : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun z => G.spacetime.horizontalMetric.inner (α z)
        (variationSquareVelocity V z.1 z.2) (variationSquareVelocity V z.1 z.2)) S := by
    intro z hz
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
      using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair z hz)).2
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hR := (H.scalar_smooth.comp_contMDiffOn hα).contDiffOn
  exact ((contDiffOn_const.mul (contDiffOn_fst.pow 2)).mul hR).add
    (contDiffOn_const.mul hg.contDiffOn)

private theorem inner_transport {q r : G.Point} (h : q = r) (v w : G.Horizontal r) :
    G.spacetime.horizontalMetric.inner q (h.symm ▸ v) (h.symm ▸ w) =
      G.spacetime.horizontalMetric.inner r v w := by
  cases h
  rfl



theorem variationActionDensity_eq_transformed (V : M14LVariationData G p R)
    {s u : ℝ} (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hu : u ∈ V.parameterDomain) :
    variationActionDensity V (s, u) =
      M14RawLIntegrand G (fun r => V.family r u) (V.family_velocity u) (s ^ 2) * (2 * s) := by
  have hs0 : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
  have heq := V.square_agrees s ⟨hs.1.le, hs.2.le⟩ u hu
  unfold variationActionDensity M14RawLIntegrand
  rw [variationSquareVelocity_eq_rescaled V hs hu, inner_transport heq, heq,
    Real.sqrt_sq hs0.le]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring




theorem variationAction_eq_squareIntegral (V : M14LVariationData G p R)
    {u : ℝ} (hu : u ∈ V.parameterDomain) :
    M14VariationAction V u =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, variationActionDensity V (s, u) := by
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := M14RawLIntegrand G (fun r => V.family r u) (V.family_velocity u))
    (continuous_id.pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le))
  have haction : M14VariationAction V u =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        M14RawLIntegrand G (fun r => V.family r u) (V.family_velocity u) (s ^ 2) * (2 * s) := by
    simpa only [Real.sq_sqrt p.tau_nonneg, Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le),
      Function.comp_def, M14VariationAction] using hsub.symm
  exact haction.trans (intervalIntegral.integral_congr_Ioo_of_le hle
    (fun _ hs => (variationActionDensity_eq_transformed V hs hu).symm))



theorem variationActionDensity_intervalIntegrable (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    IntervalIntegrable (fun s => variationActionDensity V (s, u)) MeasureTheory.volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) :=
  ((variationActionDensity_contDiffOn hM12 V).continuousOn.comp
    (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hu⟩)).intervalIntegrable_of_Icc
      (Real.sqrt_le_sqrt p.tau_lt.le)




theorem hasDerivAt_variationAction_integral (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    HasDerivAt (M14VariationAction V)
      (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (variationActionDensity V) (s, u)) u := by
  have h := M08.hasDerivAt_variationIntegral (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
    (parameterDomain_isOpen V) (variationActionDensity V)
    (variationActionDensity_contDiffOn hM12 V) hu
  apply h.congr_of_eventuallyEq
  filter_upwards [(parameterDomain_isOpen V).mem_nhds hu] with v hv
  exact variationAction_eq_squareIntegral V hv




theorem hasDerivAt_deriv_variationAction_integral (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    HasDerivAt (fun v => deriv (M14VariationAction V) v)
      (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
            (variationActionDensity V)) (s, u)) u := by
  have h := M08.hasDerivAt_deriv_variationIntegral (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
    (parameterDomain_isOpen V) (variationActionDensity V)
    (variationActionDensity_contDiffOn hM12 V) hu
  apply h.congr_of_eventuallyEq
  filter_upwards [(parameterDomain_isOpen V).mem_nhds hu] with v hv
  exact (hasDerivAt_variationAction_integral hM12 V hv).deriv.trans
    (M08.hasDerivAt_variationIntegral (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
      (parameterDomain_isOpen V) (variationActionDensity V)
      (variationActionDensity_contDiffOn hM12 V) hv).deriv.symm

end PoincareConjecture.M14
