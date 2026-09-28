import PoincareConjecture.Proofs.M76.Wall.SquareRimCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPartition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps











set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1



noncomputable def squareRimParameter (t : ℝ) : V2 :=
  (squareRimLoop.extend t : V2)



theorem squareRimParameter_apply (t : unitInterval) :
    squareRimParameter t = (squareRimLoop t : V2) :=
  congrArg Subtype.val (Path.extend_extends' squareRimLoop t)

private theorem finitePL_affine_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : ℝ →ᴬ[ℝ] E) (l u : ℝ) :
    FinitePiecewiseAffineOn A (Icc l u) := by
  classical
  let H : Finset (ℝ →ᵃ[ℝ] ℝ) :=
    {AffineMap.const ℝ ℝ l - AffineMap.id ℝ ℝ,
      AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ u}
  have hrep : Icc l u = {t | ∀ B ∈ H, B t ≤ 0} := by
    ext t
    simp [H]
  obtain ⟨K, hK, hspace⟩ := isCompact_Icc.exists_finite_triangulation_of_halfspaces H hrep
  exact ⟨K, hK, hspace, K.affineOnFaces_affine A⟩




theorem finitePiecewiseAffineOn_squareRimParameter :
    FinitePiecewiseAffineOn squareRimParameter (Icc (0 : ℝ) 1) := by
  let S (i : Fin 4) := Icc ((i : ℝ) / 4) (((i : ℝ) + 1) / 4)
  let A (i : Fin 4) : ℝ →ᴬ[ℝ] V2 :=
    (ContinuousAffineMap.lineMap (squareRimVertex i : V2) (squareRimVertex (i + 1) : V2)).comp
      ((4 : ℝ) • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ (i : ℝ))
  have hformula (i : Fin 4) : EqOn squareRimParameter (A i) (S i) := by
    intro t ht
    have hi : (i : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hnonneg : (0 : ℝ) ≤ i := by positivity
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      change (i : ℝ) / 4 ≤ t ∧ t ≤ ((i : ℝ) + 1) / 4 at ht
      constructor <;> linarith
    rw [squareRimParameter_apply ⟨t, ht01⟩, Wall.squareRimLoop_coordinates]
    change (if t ≤ 1 / 4 then ![-1 + 8 * t, -1]
      else if t ≤ 1 / 2 then ![1, -3 + 8 * t]
      else if t ≤ 3 / 4 then ![5 - 8 * t, 1]
      else ![-1, 7 - 8 * t]) =
        AffineMap.lineMap (squareRimVertex i : V2) (squareRimVertex (i + 1) : V2)
          (4 * t - (i : ℝ))
    fin_cases i <;> norm_num [S] at ht
    all_goals
      split_ifs <;> ext j <;> fin_cases j <;>
        norm_num [squareRimVertex, Fin.add_def, AffineMap.lineMap_apply_module] <;> linarith
  have hcover : (⋃ i : Fin 4, S i) = Icc (0 : ℝ) 1 := by
    ext t
    simp only [mem_iUnion, S, mem_Icc, Fin.exists_fin_succ, Fin.exists_fin_zero,
      Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    norm_num
    constructor
    · rintro (h | h | h | h) <;> constructor <;> linarith
    · intro h
      by_cases hq : t ≤ 1 / 4
      · exact Or.inl ⟨h.1, hq⟩
      · by_cases hh : t ≤ 1 / 2
        · exact Or.inr (Or.inl ⟨by linarith, hh⟩)
        · by_cases hthree : t ≤ 3 / 4
          · exact Or.inr (Or.inr (Or.inl ⟨by linarith, hthree⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by linarith, h.2⟩))
  rw [← hcover]
  exact FinitePiecewiseAffineOn.iUnion fun i =>
    (finitePL_affine_Icc (A i) _ _).congr (hformula i).symm




theorem finitePL_squareRim_composition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : V2 → E} (hf : FinitePiecewiseAffineOn f Q) :
    FinitePiecewiseAffineOn (f ∘ squareRimParameter) (Icc (0 : ℝ) 1) ∧
      ∀ t : unitInterval, (f ∘ squareRimParameter) t = f (squareRimLoop t) := by
  refine ⟨hf.comp finitePiecewiseAffineOn_squareRimParameter (fun t _ => ?_), ?_⟩
  · exact (squareRimLoop.extend t).property
  · intro t
    exact congrArg f (squareRimParameter_apply t)

end PoincareConjecture.M76.Dehn
