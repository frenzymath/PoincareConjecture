import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.CellLengthBounds
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabeledSolution
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.FamilySlope
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.IntrinsicFields









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

set_option maxHeartbeats 1200000 in





theorem m65FamilyCell_normalization_bounds (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℕ → ℝ) (h : ∀ k, 0 < circumference k)
    (hlt : ∀ k, circumference k < 1)
    (hzero : Tendsto circumference atTop (𝓝 0)) (z : LoopTwoSphere)
    {r s ell : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b) (hell : 0 < ell)
    (hlength : ∀ k, ell ≤ m62Length (G.product (circumference k) (h k)).flow
      ((C.solutions (circumference k) (h k)).curve z) r)
    (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hjets : ∀ k t x, t ∈ Icc r s → ∀ i,
      m63CurvatureJetSquared (G.product (circumference k) (h k)).flow
        ((C.solutions (circumference k) (h k)).curve z) i t x ≤ B i) :
    ∃ phi : ℕ → (ℝ ≃o ℝ),
      (∀ k, phi k 0 = 0 ∧ (∀ x, phi k (x + curvePeriod) = phi k x + curvePeriod) ∧
        ContDiff ℝ ∞ (phi k : ℝ → ℝ) ∧ (∀ x, 0 < deriv (phi k : ℝ → ℝ) x)) ∧
      let c := fun k x t => (C.solutions (circumference k) (h k)).curve z (phi k x) t
      (∀ k, M62ShrinkingCurve (G.product (circumference k) (h k)).flow (c k)) ∧
      (∀ k x, curveSpeed (G.product (circumference k) (h k)).flow (c k) r x =
        m62Length (G.product (circumference k) (h k)).flow
          ((C.solutions (circumference k) (h k)).curve z) r / curvePeriod) ∧
      ∃ vmin vmax : ℝ, 0 < vmin ∧ 0 ≤ vmax ∧
        (∀ k t x, t ∈ Icc r s → vmin ≤
          curveSpeed (G.product (circumference k) (h k)).flow (c k) t x ∧
          |curveSpeed (G.product (circumference k) (h k)).flow (c k) t x| ≤ vmax) ∧
        (∀ i, ∃ J : ℝ, 0 ≤ J ∧ ∀ k t x, t ∈ Icc r s →
          ((G.product (circumference k) (h k)).flow.metric t).tangentNorm (c k x t)
            (m65IntrinsicTangentJet (G.product (circumference k) (h k)).flow
              (c k) i t x) ≤ J) ∧
        (∀ t ∈ Icc r s, ∀ x, Tendsto
          (fun k => m62Slope (G.product (circumference k) (h k)) (c k) t x)
            atTop (𝓝 0)) := by
  classical
  have hrab := hsub (show r ∈ Icc r s from ⟨le_rfl, hrs⟩)
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  let rate := G.K2 + B 0
  have hrate : 0 ≤ rate := add_nonneg G.nonnegative.2.2 (hB 0)
  let L := C.initial_bound * Real.exp (G.K2 * (b - a))
  have hL : 0 < L := mul_pos C.initial_bound_positive (Real.exp_pos _)
  have hdist (t : ℝ) (ht : t ∈ Icc r s) : |t - r| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [hrab.1, (hsub ht).2]
  have hcurv (k : ℕ) (t : ℝ) (ht : t ∈ Icc r s) (x : ℝ) :
      m62CurvatureSquared (G.product (circumference k) (h k)).flow
        ((C.solutions (circumference k) (h k)).curve z) t x ≤ B 0 :=
    hjets k t x ht 0
  have hLupper (k : ℕ) : m62Length (G.product (circumference k) (h k)).flow
      ((C.solutions (circumference k) (h k)).curve z) r ≤ L := by
    calc
      _ ≤ (m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (r - a)) :=
        C.length_bound (circumference k) (h k) (hlt k) z r (Ioo_subset_Icc_self hrab)
      _ ≤ C.initial_bound * Real.exp (G.K2 * (r - a)) :=
        mul_le_mul_of_nonneg_right C.initial_length_bound (Real.exp_nonneg _)
      _ ≤ L := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hrab.2])
          G.nonnegative.2.2)) C.initial_bound_positive.le
  have hlowexp (t : ℝ) (ht : t ∈ Icc r s) :
      Real.exp (-rate * (b - a)) ≤ Real.exp (-rate * |t - r|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hdist t ht) (neg_nonpos.mpr hrate))
  have hupexp (t : ℝ) (ht : t ∈ Icc r s) :
      Real.exp (rate * |t - r|) ≤ Real.exp (rate * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdist t ht) hrate)
  let ell' := Real.exp (-rate * (b - a)) * ell
  have hell' : 0 < ell' := mul_pos (Real.exp_pos _) hell
  have hlowerLength (k : ℕ) (t : ℝ) (ht : t ∈ Icc r s) : ell' ≤
      m62Length (G.product (circumference k) (h k)).flow
        ((C.solutions (circumference k) (h k)).curve z) t := by
    calc
      _ ≤ Real.exp (-rate * |t - r|) * ell :=
        mul_le_mul_of_nonneg_right (hlowexp t ht) hell.le
      _ ≤ Real.exp (-rate * |t - r|) *
          m62Length (G.product (circumference k) (h k)).flow
            ((C.solutions (circumference k) (h k)).curve z) r :=
        mul_le_mul_of_nonneg_left (hlength k) (Real.exp_nonneg _)
      _ ≤ _ := (m65Length_exp_bounds_on _ ((C.solutions _ _).shrinking z)
        (G.product_bounds _ _) (convex_Icc r s) hsub (hcurv k)
        (show r ∈ Icc r s from ⟨le_rfl, hrs⟩) ht).1
  choose phi hpzero hpperiod hphi hpos hc hspeed using fun k =>
    m65ShrinkingCurve_exists_constantSpeed_solution
      ((C.solutions (circumference k) (h k)).curve z)
      ((C.solutions (circumference k) (h k)).shrinking z) hrab
  let c := fun k x t => (C.solutions (circumference k) (h k)).curve z (phi k x) t
  let vmin := Real.exp (-rate * (b - a)) * (ell / curvePeriod)
  let vmax := Real.exp (rate * (b - a)) * (L / curvePeriod)
  have hvmin : 0 < vmin := mul_pos (Real.exp_pos _) (div_pos hell hperiod)
  have hvmax : 0 < vmax := mul_pos (Real.exp_pos _) (div_pos hL hperiod)
  refine ⟨phi, fun k => ⟨hpzero k, hpperiod k, hphi k, hpos k⟩,
    hc, hspeed, vmin, vmax, hvmin, hvmax.le, ?_, ?_, ?_⟩
  · intro k t x ht
    have hcompare := m65RelabeledSpeed_exp_bounds_on
      ((C.solutions (circumference k) (h k)).curve z)
      ((C.solutions (circumference k) (h k)).shrinking z)
      (G.product_bounds _ _) (convex_Icc r s) hsub (hcurv k)
      ((hphi k).differentiable (by simp)) (hpos k)
      (show r ∈ Icc r s from ⟨le_rfl, hrs⟩) ht x
    rw [hspeed k x] at hcompare
    have hinitNonneg := (div_nonneg (hell.le.trans (hlength k)) hperiod.le)
    constructor
    · calc
        _ ≤ Real.exp (-rate * |t - r|) * (ell / curvePeriod) :=
          mul_le_mul_of_nonneg_right (hlowexp t ht) (div_nonneg hell.le hperiod.le)
        _ ≤ Real.exp (-rate * |t - r|) *
            (m62Length (G.product (circumference k) (h k)).flow
              ((C.solutions (circumference k) (h k)).curve z) r / curvePeriod) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hlength k) hperiod.le)
            (Real.exp_nonneg _)
        _ ≤ _ := hcompare.1
    · rw [abs_of_nonneg (M62.speed_nonneg _ _ _ _)]
      exact hcompare.2.trans
        ((mul_le_mul_of_nonneg_right (hupexp t ht) hinitNonneg).trans
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (hLupper k) hperiod.le) (Real.exp_nonneg _)))
  · intro i
    cases i with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro k t x ht
      exact (M62.unitTangent_norm _ (c k) (hc k) (Ioo_subset_Icc_self (hsub ht)) x).le
    | succ i =>
      refine ⟨Real.sqrt (B i), Real.sqrt_nonneg _, ?_⟩
      intro k t x ht
      have hj := m65IntrinsicJetSquared_fixed_relabeling
        ((C.solutions (circumference k) (h k)).curve z)
        ((C.solutions (circumference k) (h k)).shrinking z)
        ((C.solutions (circumference k) (h k)).intrinsic_regular z)
        ((hphi k).differentiable (by simp)) (hpos k) (hsub ht) i x
      change Real.sqrt (m63CurvatureJetSquared
        (G.product (circumference k) (h k)).flow (c k) i t x) ≤ _
      rw [hj]
      exact Real.sqrt_le_sqrt (hjets k t (phi k x) ht i)
  · intro t ht x
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    obtain ⟨delta, hdelta, hslope⟩ := m65FamilySlope_uniform_small C hell'
      (Real.sqrt_nonneg (B 0)) epsilon hepsilon
    have hsmall : ∀ᶠ k in atTop, circumference k < delta :=
      hzero.eventually (gt_mem_nhds hdelta)
    filter_upwards [hsmall] with k hk
    have hslopeBound := hslope (circumference k) (h k) hk z (Icc r s)
      (hsub.trans Ioo_subset_Icc_self) (hlowerLength k)
      (fun q hq y => Real.sqrt_le_sqrt (hcurv k q hq y)) t ht (phi k x)
    have hunit := m65UnitTangent_fixed_relabeling
      ((C.solutions (circumference k) (h k)).curve z)
      ((C.solutions (circumference k) (h k)).shrinking z)
      (((hphi k).differentiable (by simp)) x).hasDerivAt (hpos k x)
      (Ioo_subset_Icc_self (hsub ht))
    simpa only [Real.dist_eq, sub_zero, m62Slope, hunit] using hslopeBound

end PoincareConjecture
