import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Exhaustion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
  {F : RicciFlow n M J} {O : M}


lemma SmoothExhaustion.hasDerivAt_exp_mul
    (S : SmoothExhaustion F O) (ε A t : ℝ) (x : M) :
    HasDerivAt (fun s => ε * Real.exp (A * s) * S.toFun x)
      (A * (ε * Real.exp (A * t) * S.toFun x)) t := by
  simpa only [id_eq, mul_one, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).const_mul A).exp.const_mul ε).mul_const (S.toFun x)


lemma SmoothExhaustion.le_exp_mul
    (S : SmoothExhaustion F O) {ε A t : ℝ}
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (ht : 0 ≤ t) (x : M) :
    ε ≤ ε * Real.exp (A * t) * S.toFun x := by
  have he : 1 ≤ Real.exp (A * t) := Real.one_le_exp (mul_nonneg hA ht)
  calc
    ε ≤ ε * Real.exp (A * t) := by nlinarith
    _ ≤ ε * Real.exp (A * t) * S.toFun x := by
      nlinarith [S.one_le x, mul_nonneg hε (Real.exp_nonneg (A * t))]


lemma SmoothExhaustion.exp_mul_heat_gt
    (S : SmoothExhaustion F O) {ε C A t : ℝ}
    (hε : 0 < ε) (hA : C + (n : ℝ) * S.bound < A)
    (ht : t ∈ J) (x : M) :
    C * (ε * Real.exp (A * t) * S.toFun x) <
      deriv (fun s => ε * Real.exp (A * s) * S.toFun x) t -
        (F.connection t).laplacian
          (fun y => ε * Real.exp (A * t) * S.toFun y) x := by
  rw [(S.hasDerivAt_exp_mul ε A t x).deriv,
    PoincareConjecture.LeviCivitaData.laplacian_const_mul]
  have hL : 0 ≤ (n : ℝ) * S.bound := mul_nonneg (Nat.cast_nonneg _) S.bound_nonneg
  have hgap : 0 < A - C := by linarith
  have hstrict : C * S.toFun x <
      A * S.toFun x - (F.connection t).laplacian S.toFun x := by
    have hh := mul_le_mul_of_nonneg_left (S.one_le x) hgap.le
    linarith [S.laplacian_le ht x]
  have h := mul_lt_mul_of_pos_left hstrict (mul_pos hε (Real.exp_pos (A * t)))
  nlinarith



lemma SmoothExhaustion.exists_small_exp_mul
    (S : SmoothExhaustion F O) {K : Set M} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) (A T : ℝ) (hA : 0 ≤ A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 T, ∀ x ∈ K,
      ε * Real.exp (A * t) * S.toFun x ≤ η := by
  obtain ⟨L, hL⟩ := hK.bddAbove_image S.smooth.continuous.continuousOn
  let B := max L 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let ε := η / (Real.exp (A * T) * B)
  have hε : 0 < ε := div_pos hη (mul_pos (Real.exp_pos _) hB)
  refine ⟨ε, hε, ?_⟩
  intro t ht x hx
  have hh : S.toFun x ≤ B := (hL (mem_image_of_mem S.toFun hx)).trans (le_max_left _ _)
  have he : Real.exp (A * t) ≤ Real.exp (A * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hA)
  calc
    ε * Real.exp (A * t) * S.toFun x ≤ ε * Real.exp (A * T) * B :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hε.le) hh
        (by linarith [S.one_le x]) (by positivity)
    _ = η := by dsimp [ε]; field_simp



lemma SmoothExhaustion.exists_exp_barrier_coefficients
    (S : SmoothExhaustion F O) {K : Set M} (hK : IsCompact K)
    {C η T : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (hT : Icc 0 T ⊆ J) :
    ∃ A ε δ : ℝ, 0 < A ∧ 0 < ε ∧ 0 < δ ∧
      (∀ t ∈ Icc 0 T, δ ≤ δ * Real.exp (A * t) ∧
        δ * Real.exp (A * t) ≤ η) ∧
      (∀ t ∈ Icc 0 T, ∀ x, ε ≤ ε * Real.exp (A * t) * S.toFun x) ∧
      (∀ t ∈ Icc 0 T, ∀ x ∈ K,
        ε * Real.exp (A * t) * S.toFun x ≤ η) ∧
      (∀ t ∈ Icc 0 T, ∀ x,
        C * (ε * Real.exp (A * t) * S.toFun x) <
          deriv (fun s => ε * Real.exp (A * s) * S.toFun x) t -
            (F.connection t).laplacian
              (fun y => ε * Real.exp (A * t) * S.toFun y) x) ∧
      (∀ t, C * (δ * Real.exp (A * t)) <
        deriv (fun s => δ * Real.exp (A * s)) t) ∧
      (∀ t x, C * (δ * Real.exp (A * t)) ≤
        ε * Real.exp (A * t) * S.toFun x) := by
  let A := C + (n : ℝ) * S.bound + 1
  have hL : 0 ≤ (n : ℝ) * S.bound := mul_nonneg (Nat.cast_nonneg _) S.bound_nonneg
  have hA : 0 < A := by dsimp [A]; linarith
  have hAC : C < A := by dsimp [A]; linarith
  have hrate : C + (n : ℝ) * S.bound < A := by dsimp [A]; linarith
  obtain ⟨ε, hε, hsmall⟩ := S.exists_small_exp_mul
    (hK.union isCompact_singleton : IsCompact (K ∪ {O})) hη A T hA.le
  let δ := ε / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδle : δ ≤ ε := (div_le_iff₀ hden).mpr (by nlinarith)
  have hCδ : C * δ ≤ ε := by
    have heq : δ * (C + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  refine ⟨A, ε, δ, hA, hε, hδ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have he : 1 ≤ Real.exp (A * t) := Real.one_le_exp (mul_nonneg hA.le ht.1)
    refine ⟨by nlinarith, ?_⟩
    calc
      δ * Real.exp (A * t) ≤ ε * Real.exp (A * t) :=
        mul_le_mul_of_nonneg_right hδle (Real.exp_nonneg _)
      _ ≤ ε * Real.exp (A * t) * S.toFun O := by
        nlinarith [S.one_le O, mul_pos hε (Real.exp_pos (A * t))]
      _ ≤ η := hsmall t ht O (Or.inr rfl)
  · exact fun t ht x => S.le_exp_mul hε.le hA.le ht.1 x
  · exact fun t ht x hx => hsmall t ht x (Or.inl hx)
  · exact fun t ht x => S.exp_mul_heat_gt hε hrate (hT ht) x
  · intro t
    have hd : HasDerivAt (fun s => δ * Real.exp (A * s))
        (A * (δ * Real.exp (A * t))) t := by
      simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
        ((hasDerivAt_id t).const_mul A).exp.const_mul δ
    rw [hd.deriv]
    exact mul_lt_mul_of_pos_right hAC (mul_pos hδ (Real.exp_pos _))
  · intro t x
    calc
      C * (δ * Real.exp (A * t)) ≤ ε * Real.exp (A * t) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hCδ (Real.exp_nonneg (A * t))
      _ ≤ ε * Real.exp (A * t) * S.toFun x := by
        nlinarith [S.one_le x, mul_pos hε (Real.exp_pos (A * t))]




lemma SmoothExhaustion.exp_mul_div_heat_gt
    (S : SmoothExhaustion F O) {ε δ C A t : ℝ}
    (hε : 0 < ε) (hA : C + (n : ℝ) * S.bound < A)
    (ht : t ∈ J) (htpos : 0 < t) (hδ : C * δ ≤ ε) (x : M) :
    let φ := fun y s => ε * Real.exp (A * s) * S.toFun y
    let ψ := δ * Real.exp (A * t)
    C * (φ x t / t) + C * ψ / t ^ 2 <
      deriv (fun s => φ x s / s) t -
        (F.connection t).laplacian (fun y => φ y t / t) x +
          2 / t * (φ x t / t) := by
  let φ := fun y s => ε * Real.exp (A * s) * S.toFun y
  have hd := (S.hasDerivAt_exp_mul ε A t x).div (hasDerivAt_id t) htpos.ne'
  have hheat := S.exp_mul_heat_gt hε hA ht x
  have hsmall : C * (δ * Real.exp (A * t)) ≤ φ x t := by
    calc
      C * (δ * Real.exp (A * t)) ≤ ε * Real.exp (A * t) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hδ (Real.exp_nonneg (A * t))
      _ ≤ φ x t := by
        dsimp only [φ]
        exact le_mul_of_one_le_right (by positivity) (S.one_le x)
  have hdivide := div_lt_div_of_pos_right hheat htpos
  have hsmall' := div_le_div_of_nonneg_right hsmall (sq_nonneg t)
  dsimp only at ⊢
  have hd' : HasDerivAt (fun s => ε * Real.exp (A * s) * S.toFun x / s)
      ((A * (ε * Real.exp (A * t) * S.toFun x) * t -
        ε * Real.exp (A * t) * S.toFun x * 1) / t ^ 2) t := by
    simpa only [Pi.div_apply, id_eq] using! hd
  rw [hd'.deriv]
  rw [(S.hasDerivAt_exp_mul ε A t x).deriv] at hdivide
  have hlap : (F.connection t).laplacian
      (fun y => ε * Real.exp (A * t) * S.toFun y / t) x =
      (F.connection t).laplacian (fun y => ε * Real.exp (A * t) * S.toFun y) x / t := by
    simp only [div_eq_mul_inv, mul_comm _ t⁻¹,
      PoincareConjecture.LeviCivitaData.laplacian_const_mul]
  rw [hlap]
  have heq (r l : ℝ) : (A * r * t - r * 1) / t ^ 2 - l / t +
      2 / t * (r / t) = (A * r - l) / t + r / t ^ 2 := by
    field_simp
    ring
  rw [heq]
  dsimp only [φ] at hsmall'
  rw [← mul_div_assoc]
  linarith only [hdivide, hsmall']



lemma SmoothExhaustion.exp_mul_div_quadratic_heat_gt
    (S : SmoothExhaustion F O) {ε δ C A t u w : ℝ}
    (hε : 0 < ε) (hδpos : 0 < δ) (hA : C + (n : ℝ) * S.bound < A)
    (ht : t ∈ J) (htpos : 0 < t) (hδ : C * δ ≤ ε)
    (hnonzero : u ≠ 0 ∨ w ≠ 0) (x : M) :
    let α := fun y s => ε * Real.exp (A * s) * S.toFun y / s
    let ψ := fun s => δ * Real.exp (A * s)
    0 < (deriv (α x) t - (F.connection t).laplacian (fun y => α y t) x +
        2 / t * α x t - C * α x t - C * ψ t / t ^ 2) * w ^ 2 +
      (deriv ψ t - C * ψ t) * u ^ 2 := by
  have hw := S.exp_mul_div_heat_gt hε hA ht htpos hδ x
  have hd : HasDerivAt (fun s => δ * Real.exp (A * s))
      (A * (δ * Real.exp (A * t))) t := by
    simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
      ((hasDerivAt_id t).const_mul A).exp.const_mul δ
  have hAC : C < A := lt_of_le_of_lt
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) S.bound_nonneg)) hA
  have hu : 0 < deriv (fun s => δ * Real.exp (A * s)) t -
      C * (δ * Real.exp (A * t)) := by
    rw [hd.deriv]
    exact sub_pos.mpr (mul_lt_mul_of_pos_right hAC (mul_pos hδpos (Real.exp_pos _)))
  dsimp only at hw ⊢
  have hw' : 0 < deriv (fun s => ε * Real.exp (A * s) * S.toFun x / s) t -
      (F.connection t).laplacian (fun y => ε * Real.exp (A * t) * S.toFun y / t) x +
        2 / t * (ε * Real.exp (A * t) * S.toFun x / t) -
        C * (ε * Real.exp (A * t) * S.toFun x / t) -
        C * (δ * Real.exp (A * t)) / t ^ 2 := by linarith only [hw]
  rcases hnonzero with hn | hn
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hw'.le (sq_nonneg _))
      (mul_pos hu (sq_pos_of_ne_zero hn))
  · exact add_pos_of_pos_of_nonneg (mul_pos hw' (sq_pos_of_ne_zero hn))
      (mul_nonneg hu.le (sq_nonneg _))



lemma SmoothExhaustion.isCompact_exp_mul_sublevel
    (S : SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (T r : ℝ) :
    IsCompact {p : ℝ × M | p.1 ∈ Icc 0 T ∧
      ε * Real.exp (A * p.1) * S.toFun p.2 ≤ r} := by
  have hc : Continuous (fun p : ℝ × M =>
      ε * Real.exp (A * p.1) * S.toFun p.2) :=
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_fst))).mul
      (S.smooth.continuous.comp continuous_snd)
  have hclosed : IsClosed {p : ℝ × M | p.1 ∈ Icc 0 T ∧
      ε * Real.exp (A * p.1) * S.toFun p.2 ≤ r} :=
    (isClosed_Icc.preimage continuous_fst).inter (isClosed_le hc continuous_const)
  apply (isCompact_Icc.prod (hproper (r / ε))).of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, (le_div_iff₀ hε).mpr ?_⟩
  have he : 1 ≤ Real.exp (A * p.1) := Real.one_le_exp (mul_nonneg hA hp.1.1)
  have hh : 0 ≤ S.toFun p.2 := by linarith [S.one_le p.2]
  calc
    S.toFun p.2 * ε = ε * S.toFun p.2 := mul_comm _ _
    _ ≤ ε * Real.exp (A * p.1) * S.toFun p.2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) hh
    _ ≤ r := hp.2

end PoincareConjecture.RicciFlow
