import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Connection.Inverse
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Connection.Koszul



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_affine_christoffel_jet_bound
    (q : ℕ) {a : ℝ} (ha : 0 < a) (b D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E), ContDiffAt ℝ ∞ B x →
        ‖B x‖ ≤ b → (∀ v, a * ‖v‖ ^ 2 ≤ B x v v) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j B x‖ ≤ D ^ j) →
        ∀ u v, ‖iteratedFDeriv ℝ q (fun y => christoffelBilinear B y u v) x‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) * ‖u‖ * ‖v‖ := by
  obtain ⟨K, hK, hInv⟩ := exists_uniform_inverse_metric_jet_bound (E := E) q ha b D hD
  let S : ℝ := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  refine ⟨(3 / 2 : ℝ) * (K * D ^ (q + 1) * S), by positivity, ?_⟩
  intro B x hB hnorm hell hjets u v
  have hi := CoordinateTransition.isInvertible_of_uniformEllipticity ha hell
  have hInv' := hInv B x hB hnorm hell hjets
  have htop : 0 ≤ ‖iteratedFDeriv ℝ (q + 1) B x‖ := norm_nonneg _
  have hmetric (i : ℕ) (hi : i ≤ q) :
      ‖iteratedFDeriv ℝ (q - i + 1) B x‖ ≤
        D ^ (q + 1) * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) := by
    have hp : 1 ≤ D ^ (q + 1) := one_le_pow₀ hD
    by_cases hi0 : i = 0
    · subst i
      simp only [Nat.sub_zero]
      nlinarith
    · have h := (hjets (q - i + 1) (by omega) (by omega)).trans
        (pow_le_pow_right₀ hD (by omega : q - i + 1 ≤ q + 1))
      nlinarith
  have hsum : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖ *
      ‖iteratedFDeriv ℝ (q - i + 1) B x‖) ≤
      (K * D ^ (q + 1) * S) * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * K *
          (D ^ (q + 1) * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hInv' i hiq) (Nat.cast_nonneg _))
          (hmetric i hiq) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hK)
      _ = _ := by simp only [← Finset.sum_mul, S]; ring
  apply (norm_iteratedFDeriv_christoffel_apply_le hB hi q u v).trans
  calc
    _ ≤ ((3 / 2 : ℝ) * ((K * D ^ (q + 1) * S) *
        (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖))) * ‖u‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) (norm_nonneg u)) (norm_nonneg v)
    _ = _ := by ring

theorem exists_uniform_christoffel_jet_bound
    (q : ℕ) {a : ℝ} (ha : 0 < a) (b D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E), ContDiffAt ℝ ∞ B x →
        ‖B x‖ ≤ b → (∀ v, a * ‖v‖ ^ 2 ≤ B x v v) →
        (∀ j, 1 ≤ j → j ≤ q + 1 → ‖iteratedFDeriv ℝ j B x‖ ≤ D ^ j) →
        ∀ j ≤ q, ∀ u v, ‖iteratedFDeriv ℝ j (fun y => christoffelBilinear B y u v) x‖ ≤
          C * ‖u‖ * ‖v‖ := by
  classical
  choose A hA hbound using fun j : Fin (q + 1) =>
    exists_affine_christoffel_jet_bound (E := E) j.val ha b D hD
  let C : ℝ := ∑ j : Fin (q + 1), A j * (1 + D ^ (j.val + 1))
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hterm (j : Fin (q + 1)) : 0 ≤ A j * (1 + D ^ (j.val + 1)) :=
    mul_nonneg (hA j) (by positivity)
  refine ⟨C, Finset.sum_nonneg (fun j _ => hterm j), ?_⟩
  intro B x hB hnorm hell hjets j hj u v
  let k : Fin (q + 1) := ⟨j, by omega⟩
  have h := hbound k B x hB hnorm hell (fun i hi hik => hjets i hi (by omega)) u v
  have hcoef : A k * (1 + ‖iteratedFDeriv ℝ (j + 1) B x‖) ≤ C := by
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1)
      (hjets (j + 1) (by omega) (by omega))) (hA k))
    exact Finset.single_le_sum (f := fun i : Fin (q + 1) => A i * (1 + D ^ (i.val + 1)))
      (fun i _ => hterm i) (Finset.mem_univ k)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u)) (norm_nonneg v))

omit [FiniteDimensional ℝ E] in

theorem norm_iteratedFDeriv_inner_le
    {f : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x) (q : ℕ) {v : E} (hv : ‖v‖ ≤ 1) :
    ‖iteratedFDeriv ℝ q (fun y => inner ℝ v (f y)) x‖ ≤ ‖iteratedFDeriv ℝ q f x‖ := by
  have h := (innerSL ℝ v).norm_iteratedFDeriv_comp_left hf
    (show (q : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  rw [innerSL_apply_norm] at h
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hv)

theorem norm_iteratedFDeriv_christoffel_repr_le
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hB : ContDiffAt ℝ ∞ B x)
    (hi : (B x).IsInvertible) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (a : ι) (q : ℕ) (u v : E) :
    ‖iteratedFDeriv ℝ q (fun y => b.repr (christoffelBilinear B y u v) a) x‖ ≤
      ‖iteratedFDeriv ℝ q (fun y => christoffelBilinear B y u v) x‖ := by
  have hΓ := ((contDiffAt_christoffelBilinear hB hi).clm_apply
    (contDiffAt_const (c := u))).clm_apply (contDiffAt_const (c := v))
  simpa only [OrthonormalBasis.repr_apply_apply] using
    norm_iteratedFDeriv_inner_le hΓ q (le_of_eq (b.norm_eq_one a))



theorem exists_affine_christoffel_jets_bound
    (q : ℕ) {a : ℝ} (ha : 0 < a) (b D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E), ContDiffAt ℝ ∞ B x →
        ‖B x‖ ≤ b → (∀ v, a * ‖v‖ ^ 2 ≤ B x v v) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j B x‖ ≤ D ^ j) →
        ∀ j ≤ q, ∀ u v, ‖iteratedFDeriv ℝ j (fun y => christoffelBilinear B y u v) x‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) * ‖u‖ * ‖v‖ := by
  classical
  choose A hA hbound using fun j : Fin (q + 1) =>
    exists_affine_christoffel_jet_bound (E := E) j.val ha b D hD
  let C : ℝ := ∑ j : Fin (q + 1), A j * (1 + D ^ (q + 1))
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hterm (j : Fin (q + 1)) : 0 ≤ A j * (1 + D ^ (q + 1)) :=
    mul_nonneg (hA j) (by positivity)
  refine ⟨C, Finset.sum_nonneg (fun j _ => hterm j), ?_⟩
  intro B x hB hnorm hell hjets j hj u v
  let k : Fin (q + 1) := ⟨j, by omega⟩
  have h := hbound k B x hB hnorm hell (fun i hi hik => hjets i hi (by omega)) u v
  have htop : 0 ≤ ‖iteratedFDeriv ℝ (q + 1) B x‖ := norm_nonneg _
  have hp : 0 ≤ D ^ (q + 1) := pow_nonneg hD0 _
  have hmetric : 1 + ‖iteratedFDeriv ℝ (j + 1) B x‖ ≤
      (1 + D ^ (q + 1)) * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) := by
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · nlinarith
    · have hlow := (hjets (j + 1) (by omega) (by omega)).trans
        (pow_le_pow_right₀ hD (by omega : j + 1 ≤ q + 1))
      nlinarith
  have hcoef : A k * (1 + ‖iteratedFDeriv ℝ (j + 1) B x‖) ≤
      C * (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) := by
    calc
      _ ≤ A k * ((1 + D ^ (q + 1)) *
          (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖)) :=
        mul_le_mul_of_nonneg_left hmetric (hA k)
      _ = (A k * (1 + D ^ (q + 1))) *
          (1 + ‖iteratedFDeriv ℝ (q + 1) B x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i : Fin (q + 1) => A i * (1 + D ^ (q + 1)))
          (fun i _ => hterm i) (Finset.mem_univ k)) (by positivity)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u)) (norm_nonneg v))

end PoincareConjecture.SpacetimeBounds
