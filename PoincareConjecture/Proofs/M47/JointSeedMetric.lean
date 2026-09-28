import PoincareConjecture.Proofs.M35.TerminalBlowup.RicciTrace
import PoincareConjecture.Proofs.M34.Standard.NonnegativeRicciMetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {J : Set ℝ}

omit [T2Space M] in

theorem jointSeed_metric_upper_of_nonnegative_sectional
    (F : RicciFlow n M J) {b t : ℝ} (hbt : b ≤ t) (hJ : Icc b t ⊆ J)
    (hsec : ∀ s ∈ Icc b t, ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection s).curvatureTensor x v w v w)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x v v ≤ (F.metric b).inner x v v := by
  exact F.inner_self_antitoneOn_of_nonnegative_ricci (convex_Icc b t) hJ x v
    (fun s hs => M04.nonneg_ricci_of_nonnegativeSectionalAt
      (F.connection s) x (hsec s hs x) v) ⟨le_rfl, hbt⟩ ⟨hbt, le_rfl⟩ hbt

theorem jointSeed_metric_lower_of_scalar_bound
    (F : RicciFlow n M J) {b t K : ℝ} (hbt : b ≤ t) (hJ : Icc b t ⊆ J)
    (x : M)
    (hsec : ∀ s ∈ Icc b t, ∀ v w : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection s).curvatureTensor x v w v w)
    (hscalar : ∀ s ∈ Icc b t, (F.connection s).scalarCurvature x ≤ K)
    (v : TangentSpace (𝓡 n) x) :
    Real.exp (-2 * K * (t - b)) * (F.metric b).inner x v v ≤
      (F.metric t).inner x v v := by
  let q (s : ℝ) := (F.metric s).inner x v v
  let f (s : ℝ) := Real.exp (2 * K * (s - b)) * q s
  have hq (s : ℝ) : 0 ≤ q s := by
    by_cases hv : v = 0
    · simp [q, hv]
    · exact ((F.metric s).pos x v hv).le
  have hderiv (s : ℝ) (hs : s ∈ Icc b t) :
      HasDerivWithinAt f
        (Real.exp (2 * K * (s - b)) *
          (2 * K * q s - 2 * (F.connection s).ricci x v v)) (Icc b t) s := by
    convert! ((((hasDerivAt_id s).sub_const b).const_mul (2 * K)).exp.hasDerivWithinAt.mul
      ((F.equation s (hJ hs) x v v).mono hJ)) using 1
    dsimp only [f, q, id, Pi.neg_apply]
    ring
  have hmono : MonotoneOn f (Icc b t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b t)
      (fun s hs => (hderiv s hs).continuousWithinAt)
      (fun s hs => (hderiv s (interior_subset hs)).mono interior_subset)
    intro s hs
    apply mul_nonneg (Real.exp_pos _).le
    have hRic := (F.connection s).ricci_le_scalar_mul_inner_of_nonnegative_sectional
      x (hsec s (interior_subset hs)) v
    have hbound := mul_le_mul_of_nonneg_right (hscalar s (interior_subset hs)) (hq s)
    change (F.connection s).ricci x v v ≤ (F.connection s).scalarCurvature x * q s at hRic
    linarith
  have h := hmono ⟨le_rfl, hbt⟩ ⟨hbt, le_rfl⟩ hbt
  simp only [f, sub_self, mul_zero, Real.exp_zero, one_mul] at h
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-2 * K * (t - b))).le
  have hcancel : Real.exp (-2 * K * (t - b)) * Real.exp (2 * K * (t - b)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  rwa [← mul_assoc, hcancel, one_mul] at hmul

theorem jointSeed_early_metric_bounds
    (F : RicciFlow n M J) {b v A L : ℝ} {U : Set M}
    (hA : 1 ≤ A) (hL : 0 < L) (hv : 0 ≤ v) (hJ : Icc b (b + v) ⊆ J)
    (hsec : ∀ s ∈ Icc b (b + v), ∀ x : M, ∀ w z : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection s).curvatureTensor x w z w z)
    (hscalar : ∀ x ∈ U, ∀ s ∈ Icc b (b + v), (F.connection s).scalarCurvature x ≤ 8 * L)
    (hbudget : A * L * v ≤ 1 / 64) :
    ∀ s ∈ Icc b (b + v), ∀ x ∈ U, ∀ w : TangentSpace (𝓡 n) x,
      Real.exp (-1 / 4 : ℝ) * (F.metric b).inner x w w ≤ (F.metric s).inner x w w ∧
        (F.metric s).inner x w w ≤ (F.metric b).inner x w w := by
  intro s hs x hx w
  have hsub : Icc b s ⊆ Icc b (b + v) := Icc_subset_Icc le_rfl hs.2
  have hlocal := jointSeed_metric_lower_of_scalar_bound F hs.1 (hsub.trans hJ) x
    (fun u hu => hsec u (hsub hu) x) (fun u hu => hscalar x hx u (hsub hu)) w
  have hLv : L * v ≤ 1 / 64 := by
    have h := mul_le_mul_of_nonneg_right hA (mul_nonneg hL.le hv)
    nlinarith
  have hexp : Real.exp (-1 / 4 : ℝ) ≤ Real.exp (-2 * (8 * L) * (s - b)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (show s - b ≤ v by linarith [hs.2]) hL.le
    nlinarith
  have hnonneg : 0 ≤ (F.metric b).inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric b).pos x w hw).le
  exact ⟨(mul_le_mul_of_nonneg_right hexp hnonneg).trans hlocal,
    jointSeed_metric_upper_of_nonnegative_sectional F hs.1 (hsub.trans hJ)
      (fun u hu => hsec u (hsub hu)) x w⟩

end PoincareConjecture.M47
