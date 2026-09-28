import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderModelJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderComponents
import PoincareConjecture.Proofs.M34.Mathlib.CapPersistenceInverseCovariantJets

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem capPersistence_iterated_contDiffAt {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) {B : RoundCylinderTwoTensor} {x : RoundCylinderCoordinates}
    (hB : ∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b) x)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (fun y =>
      roundCylinderIteratedDerivative u (chartAt E₂ q) B k y a) x := by
  induction k with
  | zero =>
    exact (hB (a 0) (a 1)).sub
      (capPersistence_modelGram_contDiff u q (a 0) (a 1)).contDiffAt
  | succ k ih =>
    exact (((ih (fun i => a i.succ)).fderiv_right (by simp)).clm_apply
      contDiffAt_const).sub
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (capPersistence_modelChristoffel_contDiff hu q j (a 0) (a i.succ)).contDiffAt.mul
          (ih (Function.update (fun l => a l.succ) i j)))

theorem capPersistence_exists_coordinate_error_jet_bound
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta : ℝ) (B : RoundCylinderTwoTensor),
      RoundCylinderClose delta 0 B → N ≤ Nat.floor delta⁻¹ →
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-delta⁻¹) delta⁻¹ →
      ∀ j ≤ N, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
            roundCylinderGram 0 (chartAt E₂ q) y a b) (chartAt E₂ q q, s)‖ ≤
          C * Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + N)) := by
  classical
  obtain ⟨D, hD, hDb⟩ :=
    capPersistence_exists_modelChristoffel_center_jet_bound
      (by norm_num : (0 : ℝ) < 1) N
  let ell : Fin 3 → RoundCylinderCoordinates →L[ℝ] ℝ :=
    ![(EuclideanSpace.proj 0).comp (ContinuousLinearMap.fst ℝ E₂ ℝ),
      (EuclideanSpace.proj 1).comp (ContinuousLinearMap.fst ℝ E₂ ℝ),
      ContinuousLinearMap.snd ℝ E₂ ℝ]
  have hframe (v : RoundCylinderCoordinates) :
      ∑ i, ell i v • roundCylinderCoordinateBasis i = v := by
    convert sum_roundCylinderCoordinateBasis v using 1
    apply Finset.sum_congr rfl
    intro i _
    fin_cases i <;> rfl
  let L : ℝ := max 1 ((∑ i, ‖ContinuousLinearMap.smulRightL ℝ
    RoundCylinderCoordinates ℝ (ell i)‖) *
      (1 + (2 + N : ℕ) * (3 : ℝ) * (2 : ℝ) ^ N * D))
  have hL₁ : 1 ≤ L := le_max_left _ _
  refine ⟨L ^ N, pow_nonneg (zero_le_one.trans hL₁) _, ?_⟩
  intro delta B hB hN q s hs j hj a b
  let x : RoundCylinderCoordinates := (chartAt E₂ q q, s)
  let T := roundCylinderIteratedDerivative 0 (chartAt E₂ q) B
  have hxs : x ∈ (chartAt E₂ q).target ×ˢ Ioo (-delta⁻¹) delta⁻¹ :=
    ⟨(chartAt E₂ q).map_source (mem_chart_source E₂ q), hs⟩
  have hBs (a b : Fin 3) : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) y a b) x :=
    (hB.1 q a b).contDiffAt (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hxs)
  have hTs (k : ℕ) (_hk : k ≤ N) (a : Fin (2 + k) → Fin 3) :
      ContDiffAt ℝ ∞ (fun y => T k y a) x :=
    capPersistence_iterated_contDiffAt (by norm_num) q hBs k a
  have h := norm_iteratedFDeriv_le_of_covariantArray
    roundCylinderCoordinateBasis ell hframe 2 N x
    (fun y => roundCylinderChristoffel 0 (chartAt E₂ q) y) T
    (fun a b d => (capPersistence_modelChristoffel_contDiff
      (by norm_num : (0 : ℝ) < 1) q a b d).contDiffAt) hTs
    (fun _ _ _ => Filter.Eventually.of_forall fun _ => rfl)
    hD hL₁ (Real.sqrt_nonneg _)
    (by simpa only [Fintype.card_fin, Nat.cast_ofNat] using (le_max_right 1 _ : _ ≤ L))
    (fun l hl a b d => hDb q s l hl a b d)
    (fun k hk a => capPersistence_iterated_component_bound hB N hN q hs k hk a)
    0 j (by simpa using hj) ![a, b]
  change ‖iteratedFDeriv ℝ j (fun y => T 0 y ![a, b]) x‖ ≤ _
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hL₁ hj) (Real.sqrt_nonneg _))

end PoincareConjecture.M34
