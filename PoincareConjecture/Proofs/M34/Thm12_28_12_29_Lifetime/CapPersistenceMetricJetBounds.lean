import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceEuclideanJets
import PoincareConjecture.Proofs.M34.Mathlib.NeckFiniteBilinearJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)





theorem capPersistence_exists_realized_metric_jet_bound (n : ℕ) (delta : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (B : RoundCylinderTwoTensor),
      RoundCylinderClose delta 0 B → n ≤ Nat.floor delta⁻¹ →
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-delta⁻¹) delta⁻¹ →
      ∀ (g : RiemannianMetric 3 E₃),
      (∀ a b : Fin 3, (fun x => g.euclideanCoefficients x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
        =ᶠ[𝓝 (0 : E₃)] (fun x => roundCylinderTensorCoefficient B (chartAt E₂ q)
          (capPersistenceProductCoordinates x + (0, s)) a b)) →
      ∀ j ≤ n, ‖iteratedFDeriv ℝ j g.euclideanCoefficients 0‖ ≤ K := by
  obtain ⟨C, hC, hCb⟩ := capPersistence_exists_euclidean_error_jet_bound n
  obtain ⟨D, hD, hDb⟩ := exists_piLpBilinearFromCoordinates_jet_bound
    (p := 2) (q := 2) (𝕜 := ℝ) (I := Fin 3) (J := Fin 3) (E := E₃) (F := ℝ)
  let g0 := stereographicCylinderMetric 2 (by norm_num)
  obtain ⟨M, hM⟩ := Finite.exists_le
    (fun j : Fin (n + 1) => ‖iteratedFDeriv ℝ j g0.euclideanCoefficients 0‖)
  let A := C * Real.sqrt (delta ^ 2 / (1 / 2 : ℝ) ^ (2 + n))
  refine ⟨max 1 (D * A + M), le_max_left _ _, ?_⟩
  intro B hB hn q s hs g hgerm j hj
  let f : E₃ → Fin 3 → Fin 3 → ℝ := fun x a b =>
    g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) -
      g0.euclideanCoefficients x (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)
  have hf (a b : Fin 3) : ContDiffAt ℝ ∞ (fun x => f x a b) 0 :=
    (((g.contDiffAt_euclideanCoefficients 0).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).sub
      (((g0.contDiffAt_euclideanCoefficients 0).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const)
  have hb (a b : Fin 3) : ‖iteratedFDeriv ℝ j (fun x => f x a b) 0‖ ≤ A := by
    have he := (hgerm a b).sub (Filter.EventuallyEq.refl _ _ :
      (fun x : E₃ => stereographicCylinderCoefficients 2 x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
        =ᶠ[𝓝 (0 : E₃)] _)
    have hd : iteratedFDeriv ℝ j (fun x => f x a b) 0 =
        iteratedFDeriv ℝ j (fun x => roundCylinderTensorCoefficient B (chartAt E₂ q)
          (capPersistenceProductCoordinates x + (0, s)) a b -
            stereographicCylinderCoefficients 2 x
              (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
          0 := (he.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    exact hCb delta B hB hn q s hs j hj a b
  have heq : (fun x => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ) (f x)) =
      (fun x => g.euclideanCoefficients x - g0.euclideanCoefficients x) := by
    funext x
    simpa only [f, EuclideanSpace.basisFun_apply, sub_apply] using
      ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations
        (g.euclideanCoefficients x - g0.euclideanCoefficients x)
  have hbound := hDb j f 0 (fun a b => (hf a b).of_le
    (by exact_mod_cast le_top)) A hb
  rw [heq] at hbound
  change ‖iteratedFDeriv ℝ j (g.euclideanCoefficients - g0.euclideanCoefficients) 0‖ ≤ _
    at hbound
  rw [iteratedFDeriv_sub_apply
    ((g.contDiffAt_euclideanCoefficients 0).of_le (by exact_mod_cast le_top))
    ((g0.contDiffAt_euclideanCoefficients 0).of_le (by exact_mod_cast le_top))] at hbound
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g.euclideanCoefficients 0 -
          iteratedFDeriv ℝ j g0.euclideanCoefficients 0‖ +
        ‖iteratedFDeriv ℝ j g0.euclideanCoefficients 0‖ := norm_le_norm_sub_add _ _
    _ ≤ D * A + M := add_le_add hbound (hM ⟨j, by omega⟩)
    _ ≤ _ := le_max_right _ _

end PoincareConjecture.M34
