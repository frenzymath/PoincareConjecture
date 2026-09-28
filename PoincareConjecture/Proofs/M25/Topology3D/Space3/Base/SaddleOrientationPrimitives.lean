import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter
open scoped Matrix Topology

namespace PoincareConjecture.M25.Topology3D.SaddleOrientation

theorem triple_ne_zero_of_transverse
    (n u v : Fin 3 → ℝ)
    (hnu : n ⨯₃ u ≠ 0) (hv : v ≠ 0)
    (hnv : n ⬝ᵥ v = 0) (huv : u ⬝ᵥ v = 0) :
    n ⬝ᵥ (u ⨯₃ v) ≠ 0 := by
  intro hz
  let T := n ⨯₃ u
  have hcross : T ⨯₃ v = 0 := by
    dsimp only [T]
    rw [cross_cross_eq_smul_sub_smul, hnv, huv]
    simp
  have hdot : T ⬝ᵥ v = 0 := by
    calc
      T ⬝ᵥ v = v ⬝ᵥ (n ⨯₃ u) := dotProduct_comm _ _
      _ = n ⬝ᵥ (u ⨯₃ v) := triple_product_permutation v n u
      _ = 0 := hz
  have hTT : T ⬝ᵥ T ≠ 0 := by
    intro h
    exact hnu (dotProduct_self_eq_zero.mp h)
  have hvv : v ⬝ᵥ v ≠ 0 := by
    intro h
    exact hv (dotProduct_self_eq_zero.mp h)
  have hmul : (T ⬝ᵥ T) * (v ⬝ᵥ v) = 0 := by
    have h := cross_dot_cross T v T v
    simpa only [hcross, zero_dotProduct, hdot, zero_mul, sub_zero]
      using h.symm
  exact (mul_ne_zero hTT hvv) hmul

theorem dot_self_pos_of_ne_zero
    (v : Fin 3 → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have hnonneg : 0 ≤ v ⬝ᵥ v := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  apply lt_of_le_of_ne hnonneg
  intro h
  exact hv (dotProduct_self_eq_zero.mp h.symm)

theorem saddle_endpoint_gram_identity
    (n u e1 e2 : Fin 3 → ℝ) (x y lambda : ℝ)
    (hn1 : n ⬝ᵥ e1 = 0) (hn2 : n ⬝ᵥ e2 = 0)
    (hu1 : u ⬝ᵥ e1 = 2 * x) (hu2 : u ⬝ᵥ e2 = -(2 * y)) :
    let L := e1 ⨯₃ e2
    let B := y • e1 + x • e2
    (L ⬝ᵥ L) * (n ⬝ᵥ (u ⨯₃ (lambda • B))) =
      2 * lambda * (n ⬝ᵥ L) * (B ⬝ᵥ B) := by
  dsimp only
  let L := e1 ⨯₃ e2
  let B := y • e1 + x • e2
  change (L ⬝ᵥ L) * (n ⬝ᵥ (u ⨯₃ (lambda • B))) =
    2 * lambda * (n ⬝ᵥ L) * (B ⬝ᵥ B)
  have hLn : L ⨯₃ n = 0 := by
    dsimp only [L]
    rw [cross_cross_eq_smul_sub_smul,
      dotProduct_comm e1 n, dotProduct_comm e2 n, hn1, hn2]
    simp
  have hscale : (L ⬝ᵥ L) • n = (n ⬝ᵥ L) • L := by
    have h := cross_cross_eq_smul_sub_smul' L L n
    rw [hLn, map_zero] at h
    have heq := sub_eq_zero.mp h.symm
    simpa only [dotProduct_comm L n] using heq.symm
  have hLB : L ⬝ᵥ (u ⨯₃ B) = 2 * (B ⬝ᵥ B) := by
    dsimp only [L]
    rw [cross_dot_cross, dotProduct_comm e1 u,
      dotProduct_comm e2 u, hu1, hu2]
    dsimp only [B]
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm e2 e1]
    ring
  have hscaled : L ⬝ᵥ (u ⨯₃ (lambda • B)) =
      lambda * (2 * (B ⬝ᵥ B)) := by
    simp only [map_smul, dotProduct_smul, smul_eq_mul, hLB]
  calc
    (L ⬝ᵥ L) * (n ⬝ᵥ (u ⨯₃ (lambda • B))) =
        (n ⬝ᵥ L) * (L ⬝ᵥ (u ⨯₃ (lambda • B))) := by
      have h := congrArg
        (fun w : Fin 3 → ℝ => w ⬝ᵥ (u ⨯₃ (lambda • B))) hscale
      simpa only [smul_dotProduct, smul_eq_mul] using h
    _ = 2 * lambda * (n ⬝ᵥ L) * (B ⬝ᵥ B) := by
      rw [hscaled]
      ring

theorem mul_pos_of_connected_nonzero
    {X : Type*} [TopologicalSpace X] {S : Set X} {f : X → ℝ}
    (hS : IsPreconnected S) (hf : ContinuousOn f S)
    (hne : ∀ z ∈ S, f z ≠ 0)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    0 < f x * f y := by
  rcases hS.mapsTo_Ioi_or_Iio hf hne with hpos | hneg
  · exact mul_pos (hpos hx) (hpos hy)
  · exact mul_pos_of_neg_of_neg (hneg hx) (hneg hy)

theorem endpoint_lambdas_same_sign
    (L0 L1 B0 B1 J0 J1 C0 C1 lambda0 lambda1 : ℝ)
    (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hJ : 0 < J0 * J1) (hC : 0 < C0 * C1)
    (h0 : L0 * J0 = 2 * lambda0 * C0 * B0)
    (h1 : L1 * J1 = 2 * lambda1 * C1 * B1) :
    0 < lambda0 * lambda1 := by
  have hfactor : 0 < 4 * (C0 * C1) * (B0 * B1) :=
    mul_pos (mul_pos (by norm_num) hC) (mul_pos hB0 hB1)
  have hprod : 0 < (lambda0 * lambda1) *
      (4 * (C0 * C1) * (B0 * B1)) := by
    calc
      0 < (L0 * L1) * (J0 * J1) := mul_pos (mul_pos hL0 hL1) hJ
      _ = (L0 * J0) * (L1 * J1) := by ring
      _ = (2 * lambda0 * C0 * B0) *
          (2 * lambda1 * C1 * B1) := by rw [h0, h1]
      _ = (lambda0 * lambda1) *
          (4 * (C0 * C1) * (B0 * B1)) := by ring
  by_contra h
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg
    (le_of_not_gt h) hfactor.le
  exact (not_lt_of_ge hnonpos) hprod

theorem deriv_pos_of_right_increase
    {g : ℝ → ℝ} {a d : ℝ} (hd : HasDerivAt g d a)
    (hne : d ≠ 0)
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), g a ≤ g (a + t)) :
    0 < d := by
  have hnonneg : 0 ≤ d := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [hg, self_mem_nhdsWithin] with t ht htpos
    change 0 ≤ t⁻¹ * (g (a + t) - g a)
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt htpos))
      (sub_nonneg.mpr ht)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem deriv_neg_of_right_decrease
    {g : ℝ → ℝ} {a d : ℝ} (hd : HasDerivAt g d a)
    (hne : d ≠ 0)
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), g (a + t) ≤ g a) :
    d < 0 := by
  have hnonpos : d ≤ 0 := by
    apply le_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [hg, self_mem_nhdsWithin] with t ht htpos
    change t⁻¹ * (g (a + t) - g a) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (le_of_lt htpos)) (sub_nonpos.mpr ht)
  exact lt_of_le_of_ne hnonpos hne

theorem endpoint_port_products_opposite
    (lambda0 lambda1 x0 y0 x1 y1 : ℝ)
    (hlambda : 0 < lambda0 * lambda1)
    (h0 : 0 < 4 * lambda0 * x0 * y0)
    (h1 : 4 * lambda1 * x1 * y1 < 0) :
    (x0 * y0) * (x1 * y1) < 0 := by
  have hprod := mul_neg_of_pos_of_neg h0 h1
  have hfactor : 0 < 16 * (lambda0 * lambda1) :=
    mul_pos (by norm_num) hlambda
  have heq : (4 * lambda0 * x0 * y0) *
      (4 * lambda1 * x1 * y1) =
      (16 * (lambda0 * lambda1)) * ((x0 * y0) * (x1 * y1)) := by
    ring
  rw [heq] at hprod
  by_contra h
  exact (not_lt_of_ge (mul_nonneg hfactor.le (le_of_not_gt h))) hprod

end PoincareConjecture.M25.Topology3D.SaddleOrientation
