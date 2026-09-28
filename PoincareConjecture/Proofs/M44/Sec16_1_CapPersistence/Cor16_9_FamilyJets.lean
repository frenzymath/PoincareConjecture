import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsBounds
import PoincareConjecture.Definitions.Ch16.CapPersistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open M36

local notation "E" => StandardCapSpace
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance familyComparisonCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance familyComparisonCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

theorem eventually_standard_family_metricJetError_le_of_metric_eq
    {g0 : StandardInitialMetric} (S : MaximalStandardCapFlow g0)
    {H : ℝ} (hH : H < S.base.lifetime) {K : Set E} (hK : IsCompact K)
    {f : ℕ → ℝ × E → V} {J : ℕ → Set ℝ} {U : ℕ → Set E}
    (G : ℕ → ℝ → RiemannianMetric 3 E) (D : ∀ k t, LeviCivitaData (G k t))
    (hmodel : ∀ᶠ k in atTop, ∀ t ∈ J k, G k t = S.metric t)
    (m : ℕ) (hU : ∀ k, IsOpen (U k))
    (hKU : ∀ᶠ k in atTop, K ⊆ U k)
    (hJ : ∀ᶠ k in atTop, J k ⊆ Icc 0 H)
    (hsmooth : ∀ᶠ k in atTop, ∀ t ∈ J k,
      ContDiffOn ℝ ∞ (fun y => f k (t, y)) (U k))
    (hjets : ∀ j ≤ m, ∀ rho : ℝ, 0 < rho → ∀ᶠ k in atTop,
      ∀ t ∈ J k, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (fun y => f k (t, y)) x -
          iteratedFDeriv ℝ j (S.metric t).euclideanCoefficients x‖ < rho)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∀ t ∈ J k, ∀ x ∈ K,
      singularMetricJetErrorSquared (G k t) (D k t)
        (fun y v => f k (t, y) (v 0) (v 1)) m x ≤ epsilon / 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_standard_family_metricJetError_bound S hH hK m
  let rho := Real.sqrt (epsilon / (2 * C))
  have hrho : 0 < rho := Real.sqrt_pos.2 (div_pos hepsilon (by positivity))
  have hrho_sq : C * rho ^ 2 = epsilon / 2 := by
    change C * (Real.sqrt (epsilon / (2 * C))) ^ 2 = epsilon / 2
    rw [Real.sq_sqrt (div_nonneg hepsilon.le (by positivity))]
    field_simp [hC.ne']
  have hfinite : ∀ᶠ k in atTop, ∀ j : Fin (m + 1),
      ∀ t ∈ J k, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ (j : ℕ) (fun y => f k (t, y)) x -
          iteratedFDeriv ℝ (j : ℕ) (S.metric t).euclideanCoefficients x‖ < rho :=
    Filter.eventually_all.mpr (fun j => hjets j (by omega) rho hrho)
  filter_upwards [hKU, hJ, hsmooth, hfinite, hmodel] with k hkU hkJ hkS hk hkmodel
  intro t ht x hx
  have hdiff (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j
        ((fun y => f k (t, y)) - (S.metric t).euclideanCoefficients) x‖ ≤ rho := by
    change ‖iteratedFDeriv ℝ j
      (fun y => f k (t, y) - (S.metric t).euclideanCoefficients y) x‖ ≤ rho
    rw [fun_iteratedFDeriv_sub_apply
      (((hkS t ht).contDiffAt ((hU k).mem_nhds (hkU hx))).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))
      (((S.metric t).contDiffAt_euclideanCoefficients x).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))]
    exact (hk ⟨j, by omega⟩ t ht x hx).le
  have hdiff' (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j
        ((fun y => f k (t, y)) - (G k t).euclideanCoefficients) x‖ ≤ rho := by
    rw [hkmodel t ht]
    exact hdiff j hj
  exact (hbound t (hkJ ht) (G k t) (hkmodel t ht) (D k t) (U k) (hU k)
    (fun y => f k (t, y)) (hkS t ht) x hx (hkU hx) rho hrho.le hdiff').trans_eq hrho_sq

theorem eventually_standard_family_metricJetError_le
    {g0 : StandardInitialMetric} (S : MaximalStandardCapFlow g0)
    {H : ℝ} (hH : H < S.base.lifetime) {K : Set E} (hK : IsCompact K)
    {f : ℕ → ℝ × E → V} {J : ℕ → Set ℝ} {U : ℕ → Set E}
    (m : ℕ) (hU : ∀ k, IsOpen (U k))
    (hKU : ∀ᶠ k in atTop, K ⊆ U k)
    (hJ : ∀ᶠ k in atTop, J k ⊆ Icc 0 H)
    (hsmooth : ∀ᶠ k in atTop, ∀ t ∈ J k,
      ContDiffOn ℝ ∞ (fun y => f k (t, y)) (U k))
    (hjets : ∀ j ≤ m, ∀ rho : ℝ, 0 < rho → ∀ᶠ k in atTop,
      ∀ t ∈ J k, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (fun y => f k (t, y)) x -
          iteratedFDeriv ℝ j (S.metric t).euclideanCoefficients x‖ < rho)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, ∀ t ∈ J k, ∀ x ∈ K,
      singularMetricJetErrorSquared (S.metric t) (S.connection t)
        (fun y v => f k (t, y) (v 0) (v 1)) m x ≤ epsilon / 2 :=
  eventually_standard_family_metricJetError_le_of_metric_eq S hH hK
    (fun _ => S.metric) (fun _ => S.connection) (Eventually.of_forall (fun _ _ _ => rfl))
    m hU hKU hJ hsmooth hjets hepsilon

theorem singularMetricJetErrorSquared_congr_germ
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    {B C : CovariantTensorEvaluation 3 E 2} {x : E}
    (h : ∀ᶠ y in nhds x, B y = C y) (m : ℕ) :
    singularMetricJetErrorSquared g D B m x =
      singularMetricJetErrorSquared g D C m x := by
  have hdiff : ∀ᶠ y in nhds x,
      (fun v => B y v - g.inner y (v 0) (v 1)) =
        (fun v => C y v - g.inner y (v 0) (v 1)) := by
    filter_upwards [h] with y hy
    rw [hy]
  unfold singularMetricJetErrorSquared
  apply Finset.sum_congr rfl
  intro j _
  have hderiv :=
    (comparison_iteratedCovariantTensorDerivative_eventuallyEq D hdiff j).self_of_nhds
  unfold RiemannianMetric.tensorNorm
  rw [hderiv]

theorem surgeryCapFamilyComparison_of_coefficient_error
    {F : SurgeryFlowData.{u}} (S : MaximalStandardCapFlow F.standard_initial)
    {t A eta : ℝ} {I : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (chart : E → (F.slice t).carrier) {W : Set E} (hW : IsOpen W)
    (hAW : F.standard_initial.metric.ball 0 A ⊆ W)
    (B : ℝ × E → V) (bound : ℝ) (hbound : bound < eta ^ 2)
    (hlifetime : S.base.lifetime = 1)
    (htime : ∀ s ∈ I, s ∈ Ico 0 S.base.lifetime)
    (himage : chart '' F.standard_initial.metric.ball 0 A = U)
    (hread : ∀ s (hs : s ∈ I), ∀ y ∈ W, ∀ v w : E,
      B (s, y) v w = e.pullbackInner s hs (chart y)
        (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y w))
    (herror : ∀ s ∈ I, ∀ x ∈ F.standard_initial.metric.ball 0 A,
      singularMetricJetErrorSquared (S.metric s) (S.connection s)
        (fun y v => B (s, y) (v 0) (v 1)) ⌊eta⁻¹⌋₊ x ≤ bound) :
    SurgeryCapFamilyComparison F S A eta e chart := by
  refine ⟨bound, hbound, hlifetime, htime, himage, ?_⟩
  intro s hs x hx
  have heq : (fun y (v : Fin 2 → E) => B (s, y) (v 0) (v 1)) =ᶠ[nhds x]
      (fun y v => e.pullbackInner s hs (chart y)
        (mfderiv (𝓡 3) (𝓡 3) chart y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) chart y (v 1))) := by
    filter_upwards [hW.mem_nhds (hAW hx)] with y hy
    funext v
    exact hread s hs y hy (v 0) (v 1)
  exact (singularMetricJetErrorSquared_congr_germ (S.metric s) (S.connection s)
    (x := x) heq ⌊eta⁻¹⌋₊).symm.trans_le (herror s hs x hx)

end PoincareConjecture.M44
