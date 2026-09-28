import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderOrdinaryJets
import PoincareConjecture.Proofs.M34.Mathlib.NeckCovariantArrayBounds











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)




theorem capPersistence_exists_intrinsic_error_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : RoundCylinderTwoTensor) (q : UnitTwoSphere) (s : ℝ),
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b) (0, s)) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ N, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ A) →
      roundCylinderJetErrorSquared 0 B N (q, s) ≤ C * A ^ 2 := by
  obtain ⟨D, hD, hDb⟩ := capPersistence_exists_modelChristoffel_center_jet_bound
    (by norm_num : (0 : ℝ) < 1) N
  let L : ℝ := max 1 ((∑ i : Fin 3,
    ‖ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)‖) +
      (2 + N : ℕ) * 3 * (2 : ℝ) ^ N * D)
  have hL : 1 ≤ L := le_max_left _ _
  let W : ℝ := ∑ k ∈ Finset.range (N + 1), ((3 : ℝ) ^ (2 + k)) ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun k _ => sq_nonneg _
  refine ⟨W * (L ^ N) ^ 2, mul_nonneg hW (sq_nonneg _), ?_⟩
  intro B q s hBs A hA hb
  let x : RoundCylinderCoordinates := (0, s)
  let T := roundCylinderIteratedDerivative 0 (chartAt E₂ q) B
  have hTs (k : ℕ) (_hk : k ≤ N) (a : Fin (2 + k) → Fin 3) :
      ContDiffAt ℝ ∞ (fun y => T k y a) x :=
    capPersistence_iterated_contDiffAt (by norm_num) q hBs k a
  have hΓ (j : ℕ) (hj : j ≤ N) (a b d : Fin 3) :
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderChristoffel 0 (chartAt E₂ q) y a b d) x‖ ≤ D := by
    simpa only [sphere_chart_center_zero] using hDb q s j hj a b d
  have hcomponent (k : ℕ) (hk : k ≤ N) (a : Fin (2 + k) → Fin 3) :
      |T k x a| ≤ L ^ N * A := by
    have hh := norm_covariantArray_jet_le_of_total_order roundCylinderCoordinateBasis
      2 N x (roundCylinderChristoffel 0 (chartAt E₂ q)) T
      (fun i j d => (capPersistence_modelChristoffel_contDiff
        (by norm_num : (0 : ℝ) < 1) q i j d).contDiffAt) hTs
      (fun _ _ _ => Filter.Eventually.of_forall fun _ => rfl) hD hL hA
      (by simpa only [Fintype.card_fin, Nat.cast_ofNat] using (le_max_right 1 _ : _ ≤ L))
      hΓ (fun j hj a => hb j hj (a 0) (a 1)) k 0 (by simpa using hk) a
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hk) hA)
  have hinv (i j : Fin 3) :
      |(roundCylinderGram 0 (chartAt E₂ q) (chartAt E₂ q q, s))⁻¹ i j| ≤ 1 := by
    have hh := roundCylinderGram_chart_center_inv_le (by norm_num : (0 : ℝ) < 1)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 0 from ⟨le_rfl, le_rfl⟩) q s i j
    have hm : max (1 : ℝ) ((2 * (1 - (0 : ℝ)))⁻¹) = 1 := by norm_num
    rwa [hm] at hh
  have he := roundCylinderJetErrorSquared_le (B := B) (order := N) (z := (q, s))
    zero_le_one hinv (fun k hk a => by
      simpa only [sphere_chart_center_zero] using hcomponent k hk a)
  simp only [one_pow, mul_one] at he
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), ((3 : ℝ) ^ (2 + k)) ^ 2 * (L ^ N * A) ^ 2 := he
    _ = W * (L ^ N * A) ^ 2 := (Finset.sum_mul ..).symm
    _ = _ := by ring

end PoincareConjecture.M34
