import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M04.TensorNormBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem metric_comparison_of_curvature_bound {J : Set ℝ}
    (F : RicciFlow n M J) {s t K : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hst : s ≤ t) (hK : 0 ≤ K)
    (hRm : ∀ τ ∈ Set.Icc s t, ∀ x : M, (F.connection τ).curvatureTensorNorm x ≤ K)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    Real.exp (-2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v ≤
        (F.metric t).inner x v v ∧
      (F.metric t).inner x v v ≤
        Real.exp (2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v := by
  let q := fun τ ↦ (F.metric τ).inner x v v
  let c := 2 * (n : ℝ) * K
  have hJI : Set.Icc s t ⊆ J := F.interval.out hs ht
  have hq0 (τ : ℝ) : 0 ≤ q τ := by
    by_cases hv : v = 0
    · simp [q, hv]
    · exact (F.metric τ).pos x v hv |>.le
  have hqD (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      HasDerivWithinAt q (-2 * (F.connection τ).ricci x v v) (Set.Icc s t) τ :=
    (F.equation τ (hJI hτ) x v v).mono hJI
  have hBound (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      -c * q τ ≤ -2 * (F.connection τ).ricci x v v ∧
        -2 * (F.connection τ).ricci x v v ≤ c * q τ := by
    have h := (M04.abs_ricci_le_curvatureTensorNorm (F.connection τ) x v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hRm τ hτ x) (Nat.cast_nonneg n)) (hq0 τ))
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK
    have h0 := mul_nonneg hnK (hq0 τ)
    obtain ⟨hl, hu⟩ := abs_le.mp h
    dsimp only [c, q] at *
    constructor <;> nlinarith
  let p := fun τ ↦ Real.exp (c * (τ - s)) * q τ
  let m := fun τ ↦ Real.exp (-(c * (τ - s))) * q τ
  have hpD (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      HasDerivWithinAt p
        (Real.exp (c * (τ - s)) * (c * q τ - 2 * (F.connection τ).ricci x v v))
        (Set.Icc s t) τ := by
    convert! ((((hasDerivAt_id τ).sub_const s).const_mul c).exp.hasDerivWithinAt.mul
      (hqD τ hτ)) using 1
    dsimp only [id, Pi.neg_apply]
    ring
  have hmD (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
      HasDerivWithinAt m
        (Real.exp (-(c * (τ - s))) * (-2 * (F.connection τ).ricci x v v - c * q τ))
        (Set.Icc s t) τ := by
    convert! (((((hasDerivAt_id τ).sub_const s).const_mul c).neg.exp.hasDerivWithinAt).mul
      (hqD τ hτ)) using 1
    dsimp only [id, Pi.neg_apply]
    ring
  have hp : MonotoneOn p (Set.Icc s t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t)
      (fun τ hτ ↦ (hpD τ hτ).continuousWithinAt)
      (fun τ hτ ↦ (hpD τ (interior_subset hτ)).mono interior_subset)
    intro τ hτ
    apply mul_nonneg (Real.exp_pos _).le
    have h := (hBound τ (interior_subset hτ)).1
    linarith
  have hm : AntitoneOn m (Set.Icc s t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
      (fun τ hτ ↦ (hmD τ hτ).continuousWithinAt)
      (fun τ hτ ↦ (hmD τ (interior_subset hτ)).mono interior_subset)
    intro τ hτ
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have h := (hBound τ (interior_subset hτ)).2
    linarith
  have hp' : q s ≤ Real.exp (c * (t - s)) * q t := by
    simpa only [p, sub_self, mul_zero, Real.exp_zero, one_mul] using
      hp ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  have hm' : Real.exp (-(c * (t - s))) * q t ≤ q s := by
    simpa only [m, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] using
      hm ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  constructor
  · have h := mul_le_mul_of_nonneg_left hp' (Real.exp_pos (-(c * (t - s)))).le
    have he : Real.exp (-(c * (t - s))) * Real.exp (c * (t - s)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [← mul_assoc, he, one_mul] at h
    simpa only [c, q, neg_mul] using h
  · have h := mul_le_mul_of_nonneg_left hm' (Real.exp_pos (c * (t - s))).le
    have he : Real.exp (c * (t - s)) * Real.exp (-(c * (t - s))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [← mul_assoc, he, one_mul] at h
    exact h

end PoincareConjecture.RicciFlow

