import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderOrdinaryJets
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderCharts
import PoincareConjecture.Proofs.M34.Mathlib.LinearPrecomposeLocalJets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable def capPersistenceProductCoordinates : E₃ →L[ℝ] RoundCylinderCoordinates :=
  cylinderHorizontal.prod (EuclideanSpace.proj 2)

theorem capPersistenceProductCoordinates_basis (a : Fin 3) :
    capPersistenceProductCoordinates (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      roundCylinderCoordinateBasis a := by
  apply Prod.ext
  · ext i
    fin_cases a <;> fin_cases i <;>
      simp [capPersistenceProductCoordinates, cylinderHorizontal_apply,
        EuclideanSpace.basisFun_apply, roundCylinderCoordinateBasis]
  · fin_cases a <;>
      simp [capPersistenceProductCoordinates, EuclideanSpace.basisFun_apply,
        roundCylinderCoordinateBasis]

theorem capPersistence_gram_productCoordinates (q : UnitTwoSphere) (s : ℝ)
    (x : E₃) (a b : Fin 3) :
    roundCylinderGram 0 (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) a b =
      stereographicCylinderCoefficients 2 x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  rw [roundCylinderGram_chosenChart, stereographicCylinderCoefficients_apply]
  have hd : ‖cylinderHorizontal x‖ ^ 2 + 4 = stereographicCylinderDenominator x := by
    rw [cylinderHorizontal_norm_sq]
    dsimp [stereographicCylinderDenominator]
    ring
  simp only [capPersistenceProductCoordinates, ContinuousLinearMap.prod_apply,
    Prod.fst_add, add_zero, hd]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.diagonal, stereographicCylinderDensity, EuclideanSpace.basisFun_apply]

theorem capPersistence_exists_euclidean_error_jet_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta : ℝ) (B : RoundCylinderTwoTensor),
      RoundCylinderClose delta 0 B → N ≤ Nat.floor delta⁻¹ →
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-delta⁻¹) delta⁻¹ →
      ∀ j ≤ N, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun x =>
        roundCylinderTensorCoefficient B (chartAt E₂ q)
            (capPersistenceProductCoordinates x + (0, s)) a b -
          stereographicCylinderCoefficients 2 x (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b)) (0 : E₃)‖ ≤
        C * Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + N)) := by
  obtain ⟨C, hC, hCb⟩ := capPersistence_exists_coordinate_error_jet_bound N
  let L := capPersistenceProductCoordinates
  let K := max 1 ‖L‖
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨C * K ^ N, mul_nonneg hC (pow_nonneg (zero_le_one.trans hK) _), ?_⟩
  intro delta B hB hN q s hs j hj a b
  let f : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
      roundCylinderGram 0 (chartAt E₂ q) y a b
  let fs := fun y : RoundCylinderCoordinates => f (y + (0, s))
  have hxs : (0, s) ∈ (chartAt E₂ q).target ×ˢ Ioo (-delta⁻¹) delta⁻¹ := by
    refine ⟨?_, hs⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  have hf : ContDiffAt ℝ ∞ f (0, s) :=
    ((hB.1 q a b).contDiffAt
      (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hxs)).sub
      (capPersistence_modelGram_contDiff 0 q a b).contDiffAt
  have hfs : ContDiffAt ℝ ∞ fs (L 0) := by
    rw [map_zero]
    have ha : ContDiffAt ℝ ∞ (fun y : RoundCylinderCoordinates => y + (0, s)) 0 :=
      contDiffAt_id.add contDiffAt_const
    have hf' : ContDiffAt ℝ ∞ f ((0 : RoundCylinderCoordinates) + (0, s)) := by
      simpa only [zero_add] using hf
    exact hf'.comp 0 ha
  have heq : (fun x : E₃ =>
      roundCylinderTensorCoefficient B (chartAt E₂ q) (L x + (0, s)) a b -
        stereographicCylinderCoefficients 2 x (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) = fs ∘ L := by
    funext x
    dsimp only [Function.comp_apply, fs, f]
    rw [capPersistence_gram_productCoordinates]
  rw [heq]
  have h := L.norm_iteratedFDeriv_comp_right_of_contDiffAt
    (hfs.of_le (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞))
  have hb : ‖iteratedFDeriv ℝ j fs (L 0)‖ ≤
      C * Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + N)) := by
    rw [map_zero, iteratedFDeriv_comp_add_right, zero_add]
    simpa only [sphere_chart_center_zero] using hCb delta B hB hN q s hs j hj a b
  have hp : ‖L‖ ^ j ≤ K ^ N :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hK hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j fs (L 0)‖ * ‖L‖ ^ j := h
    _ ≤ (C * Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + N))) * K ^ N :=
      mul_le_mul hb hp (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

end PoincareConjecture.M34
