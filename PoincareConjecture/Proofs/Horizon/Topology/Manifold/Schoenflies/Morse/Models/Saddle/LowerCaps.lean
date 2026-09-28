import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Shear
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

def vector (x y z : Real) : E3 := WithLp.toLp 2 ![x, y, z]

@[simp] theorem vector_zero (x y z : Real) : vector x y z 0 = x := rfl
@[simp] theorem vector_one (x y z : Real) : vector x y z 1 = y := rfl
@[simp] theorem vector_two (x y z : Real) : vector x y z 2 = z := rfl

theorem norm_sq_two (q : E2) : ‖q‖ ^ 2 = (q 0) ^ 2 + (q 1) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

def lowerDomain : Set E2 := {q | (q 0) ^ 2 + (q 1 - 1 / 2) ^ 2 < 1}

def lowerCap (σ : Real) (q : E2) : E3 :=
  vector (σ * Real.sqrt (1 - (q 0) ^ 2 - (q 1 - 1 / 2) ^ 2))
    (q 0) ((q 0) ^ 2 + (q 1) ^ 2 - 5 / 4)

theorem isOpen_lowerDomain : IsOpen lowerDomain :=
  isOpen_lt (by fun_prop) continuous_const

theorem lowerCap_contDiffOn (σ : Real) : ContDiffOn Real ∞ (lowerCap σ) lowerDomain := by
  have hs : ContDiffOn Real ∞
      (fun q : E2 => Real.sqrt (1 - (q 0) ^ 2 - (q 1 - 1 / 2) ^ 2)) lowerDomain :=
    (by fun_prop : ContDiff Real ∞
      (fun q : E2 => 1 - (q 0) ^ 2 - (q 1 - 1 / 2) ^ 2)).contDiffOn.sqrt
      (fun q hq => ne_of_gt (by change (q 0)^2 + (q 1 - 1/2)^2 < 1 at hq; linarith))
  have hvec (x y z : Real) : vector x y z =
      x • EuclideanSpace.single 0 1 + y • EuclideanSpace.single 1 1 +
        z • EuclideanSpace.single 2 1 := by
    ext i
    fin_cases i <;> simp [vector]
  unfold lowerCap
  simp only [hvec]
  exact (((contDiffOn_const.mul hs).smul contDiffOn_const).add
    (((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.contDiffOn).smul
      contDiffOn_const)).add
    ((by fun_prop : ContDiff Real ∞
      (fun q : E2 => (q 0) ^ 2 + (q 1) ^ 2 - 5 / 4)).contDiffOn.smul contDiffOn_const)

theorem lowerCap_height (σ : Real) (q : E2) : lowerCap σ q 2 = ‖q‖ ^ 2 - 5 / 4 := by
  simp [lowerCap, norm_sq_two]

theorem lowerCap_first_sq {σ : Real} (hσ : σ ^ 2 = 1) {q : E2}
    (hq : q ∈ lowerDomain) :
    (lowerCap σ q 0) ^ 2 = 1 - (q 0) ^ 2 - (q 1 - 1 / 2) ^ 2 := by
  have hpos : 0 ≤ 1 - (q 0) ^ 2 - (q 1 - 1 / 2) ^ 2 := by
    change (q 0)^2 + (q 1 - 1/2)^2 < 1 at hq
    linarith
  change (σ * Real.sqrt _) ^ 2 = _
  rw [mul_pow, hσ, one_mul, Real.sq_sqrt hpos]

theorem lowerCap_inverse_coordinate {σ : Real} (hσ : σ ^ 2 = 1) {q : E2}
    (hq : q ∈ lowerDomain) :
    lowerCap σ q 2 + (lowerCap σ q 0) ^ 2 + 1 / 2 = q 1 := by
  rw [lowerCap_first_sq hσ hq]
  simp only [lowerCap, vector_two]
  ring

theorem lowerCap_mem_surface {σ : Real} (hσ : σ ^ 2 = 1) {q : E2}
    (hq : q ∈ lowerDomain) : polynomial (lowerCap σ q) = 1 := by
  have hfirst := lowerCap_first_sq hσ hq
  have hinv := lowerCap_inverse_coordinate hσ hq
  unfold polynomial
  have hz : lowerCap σ q 2 + (lowerCap σ q 0)^2 = q 1 - 1/2 := by linarith
  rw [hz, hfirst]
  simp [lowerCap]
  ring

theorem lowerCap_injOn {σ : Real} (hσ : σ ^ 2 = 1) : InjOn (lowerCap σ) lowerDomain := by
  intro q hq r hr heq
  have hx : q 0 = r 0 := congrArg (fun p : E3 => p 1) heq
  have hy : q 1 = r 1 := by
    rw [← lowerCap_inverse_coordinate hσ hq, ← lowerCap_inverse_coordinate hσ hr, heq]
  ext i
  fin_cases i <;> assumption

theorem lower_closedBall_subset_domain :
    closedBall (0 : E2) (Real.sqrt (1 / 8)) ⊆ lowerDomain := by
  intro q hq
  have hn := mem_closedBall_zero_iff.mp hq
  have hs : (q 0)^2 + (q 1)^2 ≤ 1/8 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1/8)
    rw [← norm_sq_two]
    nlinarith [norm_nonneg q, Real.sqrt_nonneg (1/8)]
  change (q 0)^2 + (q 1 - 1/2)^2 < 1
  have hy : -(1/2 : Real) < q 1 := by nlinarith [sq_nonneg (q 0)]
  nlinarith

theorem lowerCap_boundary_height (σ : Real) {q : E2}
    (hq : q ∈ sphere (0 : E2) (Real.sqrt (1/8))) : lowerCap σ q 2 = -9/8 := by
  rw [lowerCap_height, mem_sphere_zero_iff_norm.mp hq, Real.sq_sqrt (by norm_num)]
  norm_num

def lowerCoordinates (p : E3) : E2 := WithLp.toLp 2 ![p 1, p 2 + (p 0)^2 + 1/2]

theorem lowerCoordinates_contDiff : ContDiff Real ∞ lowerCoordinates := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff Real ∞ (fun p : E3 => p 1)
    fun_prop
  · change ContDiff Real ∞ (fun p : E3 => p 2 + (p 0)^2 + 1/2)
    fun_prop

theorem lowerCoordinates_lowerCap {σ : Real} (hσ : σ^2 = 1) {q : E2}
    (hq : q ∈ lowerDomain) : lowerCoordinates (lowerCap σ q) = q := by
  ext i
  fin_cases i
  · rfl
  · exact lowerCap_inverse_coordinate hσ hq

theorem lowerCap_fderiv_injective {σ : Real} (hσ : σ^2 = 1) {q : E2}
    (hq : q ∈ lowerDomain) : Injective (fderiv Real (lowerCap σ) q) := by
  have heq : lowerCoordinates ∘ lowerCap σ =ᶠ[𝓝 q] id :=
    Filter.eventually_of_mem (isOpen_lowerDomain.mem_nhds hq)
      (fun r hr => lowerCoordinates_lowerCap hσ hr)
  have hc := heq.fderiv_eq (𝕜 := Real)
  rw [fderiv_comp q (lowerCoordinates_contDiff.differentiable (by simp) _)
    (((lowerCap_contDiffOn σ q hq).contDiffAt (isOpen_lowerDomain.mem_nhds hq)).differentiableAt
      (by simp)), fderiv_id] at hc
  intro x y hxy
  have h := congrArg (fun L : E2 →L[Real] E2 => L x) hc
  have h' := congrArg (fun L : E2 →L[Real] E2 => L y) hc
  change fderiv Real lowerCoordinates (lowerCap σ q) (fderiv Real (lowerCap σ) q x) = x at h
  change fderiv Real lowerCoordinates (lowerCap σ q) (fderiv Real (lowerCap σ) q y) = y at h'
  rw [hxy] at h
  exact h.symm.trans h'

theorem lowerCoordinates_norm_sq {p : E3} (hp : polynomial p = 1) :
    ‖lowerCoordinates p‖ ^ 2 = p 2 + 5/4 := by
  rw [norm_sq_two]
  change (p 1)^2 + (p 2 + (p 0)^2 + 1/2)^2 = _
  unfold polynomial at hp
  nlinarith

theorem lowerCap_image_closedBall {σ : Real} (hσ : σ ^ 2 = 1) :
    lowerCap σ '' closedBall (0 : E2) (Real.sqrt (1/8)) =
      {p | polynomial p = 1 ∧ p 2 ≤ -9/8 ∧ 0 ≤ σ * p 0} := by
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    refine ⟨lowerCap_mem_surface hσ (lower_closedBall_subset_domain hq), ?_, ?_⟩
    · rw [lowerCap_height]
      have hn := mem_closedBall_zero_iff.mp hq
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1/8),
        norm_nonneg q, Real.sqrt_nonneg (1/8)]
    · change 0 ≤ σ * (σ * Real.sqrt _)
      rw [← mul_assoc, ← pow_two, hσ, one_mul]
      exact Real.sqrt_nonneg _
  · intro p hp
    let q := lowerCoordinates p
    have hq : q ∈ closedBall (0 : E2) (Real.sqrt (1/8)) := by
      rw [mem_closedBall_zero_iff]
      have hn : ‖q‖^2 = p 2 + 5/4 := lowerCoordinates_norm_sq hp.1
      nlinarith [hp.2.1, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1/8),
        norm_nonneg q, Real.sqrt_nonneg (1/8)]
    refine ⟨q, hq, ?_⟩
    have hp' := hp.1
    unfold polynomial at hp'
    have hr : 1 - (q 0)^2 - (q 1 - 1/2)^2 = (p 0)^2 := by
      change 1 - (p 1)^2 - (p 2 + (p 0)^2 + 1/2 - 1/2)^2 = _
      nlinarith
    have hx : lowerCap σ q 0 = p 0 := by
      change σ * Real.sqrt _ = _
      rw [hr, Real.sqrt_sq_eq_abs]
      rcases sq_eq_one_iff.mp hσ with hσ | hσ
      · rw [hσ] at hp ⊢
        have hn : 0 ≤ p 0 := by simpa only [one_mul] using hp.2.2
        rw [one_mul, abs_of_nonneg hn]
      · rw [hσ] at hp ⊢
        have hn : p 0 ≤ 0 := by linarith [hp.2.2]
        rw [abs_of_nonpos hn]
        ring
    ext i
    fin_cases i
    · exact hx
    · rfl
    · change lowerCap σ q 2 = p 2
      rw [lowerCap_height, lowerCoordinates_norm_sq hp.1]
      ring

theorem lowerCaps_disjoint :
    Disjoint (lowerCap 1 '' closedBall (0 : E2) (Real.sqrt (1/8)))
      (lowerCap (-1) '' closedBall (0 : E2) (Real.sqrt (1/8))) := by
  rw [lowerCap_image_closedBall (by norm_num : (1 : Real)^2 = 1),
    lowerCap_image_closedBall (by norm_num : (-1 : Real)^2 = 1)]
  apply disjoint_left.mpr
  intro p hp hm
  have hx : p 0 = 0 := by nlinarith [hp.2.2, hm.2.2]
  have heq := hp.1
  unfold polynomial at heq
  rw [hx] at heq
  nlinarith [hp.2.1, sq_nonneg (p 1)]

end Poincare.Manifold.Schoenflies.Saddle
