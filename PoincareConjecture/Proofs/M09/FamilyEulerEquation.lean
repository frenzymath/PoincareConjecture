import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Proofs.M09.LocalRegularizedEquation

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem lExponentialFamily_localRegularizedEquation
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (s : ℝ) (hs : s ∈ Set.Ioo 0 (Real.sqrt b)) :
    LocalRegularizedEquation F T (A.squareFamily Z) s := by
  let R := A.regularization Z b hb hmax
  let K := sqrtParameterInterval 0 b
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb)
  have hsK : s ∈ K := by rw [hK]; exact Set.Ioo_subset_Icc_self hs
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans hs.1,
      hs.2.trans (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hlocal := (regularizedEquation_iff_local F hM04 T τmax hτmax hwindow
    R.path.curve R.path.domain K R.path.open_domain R.path.interval_subset hKdiff
    R.path.smooth R.velocity_extension s hsK htime).mp (R.equation s hsK)
  have heq : Set.EqOn R.path.curve (A.squareFamily Z) K := by
    intro r hr
    have hr0 : 0 ≤ r := by simpa only [Real.sqrt_zero] using hr.1
    have hrmax : r < Real.sqrt τmax :=
      hr.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact (R.path.agrees r hr).trans
      ((congrFun (A.path_eq Z b hb hmax) (r ^ 2)).trans
        (A.square_agrees Z r ⟨hr0, hrmax⟩).symm)
  apply hlocal.congr
  apply Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
  intro r hr
  apply heq
  rw [hK]
  exact Set.Ioo_subset_Icc_self hr

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_firstVariationResidualIntegral_eq_zero
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (V : LVariation F T 0 b (A.path Z b hb hmax)) (D : LVariationDerivativeData V) :
    firstVariationResidualIntegral V D = 0 := by
  let K := sqrtParameterInterval 0 b
  let U : Set ℝ := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  have hzero : (0 : ℝ) ∈ Set.Ioo (-V.radius) V.radius :=
    ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb)
  have hU : IsOpen U := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hKU : K ⊆ U := fun s hs ↦ V.square_contains ⟨hs, hzero⟩
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun s (hs : s ∈ U) ↦ hs)
  have heq : Set.EqOn V.baseSquareCurve (A.squareFamily Z) K := by
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    have hsmax : s < Real.sqrt τmax :=
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact (V.square_agrees s hs 0 hzero).trans ((V.at_zero (s ^ 2)).trans
      ((congrFun (A.path_eq Z b hb hmax) (s ^ 2)).trans
        (A.square_agrees Z s ⟨hs0, hsmax⟩).symm))
  have hresidual : ∀ s ∈ Set.Ioo 0 (Real.sqrt b),
      -regularizedEulerResidual F T V.baseSquareCurve K D.velocity_extension s
        (squareVariationField V s) = 0 := by
    intro s hs
    have hsK : s ∈ K := by rw [hK]; exact Set.Ioo_subset_Icc_self hs
    have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
      ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans hs.1,
        hs.2.trans (Real.sqrt_lt_sqrt hb.le hmax)⟩
    have hgerm : V.baseSquareCurve =ᶠ[nhds s] A.squareFamily Z := by
      apply Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
      intro r hr
      apply heq
      rw [hK]
      exact Set.Ioo_subset_Icc_self hr
    have hlocal := (lExponentialFamily_localRegularizedEquation hM04 hτmax hwindow
      A Z b hb hmax s hs).congr hgerm.symm
    have heuler := (regularizedEquation_iff_local F hM04 T τmax hτmax hwindow
      V.baseSquareCurve U K hU hKU hKdiff hβ D.velocity_extension s hsK htime).mpr hlocal
    exact neg_eq_zero.mpr (heuler (squareVariationField V s))
  unfold firstVariationResidualIntegral
  rw [Real.sqrt_zero]
  calc
    _ = ∫ _s in (0 : ℝ)..Real.sqrt b, (0 : ℝ) :=
      intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_nonneg b) hresidual
    _ = 0 := by simp

end PoincareConjecture.Proofs.M09
