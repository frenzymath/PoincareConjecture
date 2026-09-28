import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "C8" => AddCircle (4 * (2 : ℝ))

private noncomputable def squareCenter : (ℝ × ℝ) ≃ᴬ[ℝ] V2 :=
  (ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-1, -1)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousAffineEquiv

private theorem squareCenter_apply (p : ℝ × ℝ) :
    squareCenter p = ![-1 + p.1, -1 + p.2] := rfl

private theorem squareCenter_mem (p : ℝ × ℝ) :
    squareCenter p ∈ Q ↔ p ∈ PLAnnularStrip.squareAnnulus 2 0 := by
  have hle : ‖squareCenter p‖ ≤ 1 ↔
      p.1 ∈ Icc (0 : ℝ) 2 ∧ p.2 ∈ Icc (0 : ℝ) 2 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    simp only [squareCenter_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, abs_le, mem_Icc]
    constructor <;> rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩ <;>
      constructor <;> constructor <;> linarith
  have hlt : ‖squareCenter p‖ < 1 ↔
      p.1 ∈ Ioo (0 : ℝ) 2 ∧ p.2 ∈ Ioo (0 : ℝ) 2 := by
    rw [pi_norm_lt_iff (by norm_num)]
    simp only [squareCenter_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, abs_lt, mem_Ioo]
    constructor <;> rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩ <;>
      constructor <;> constructor <;> linarith
  rw [mem_sphere_zero_iff_norm, show ‖squareCenter p‖ = 1 ↔
    ‖squareCenter p‖ ≤ 1 ∧ ¬ ‖squareCenter p‖ < 1 by
      constructor
      · intro h; exact ⟨h.le, not_lt.mpr h.ge⟩
      · rintro ⟨h, h'⟩; exact le_antisymm h (le_of_not_gt h'), hle, hlt]
  simp only [PLAnnularStrip.squareAnnulus, neg_zero, add_zero, sub_zero,
    mem_sdiff, mem_prod]

private theorem exists_squareCircle :
    ∃ zeta : C8 ≃ₜ Q, ∀ z : C8,
      (zeta z : V2) = squareCenter (PLAnnularStrip.annulusMap 2 (by norm_num) (z, 0)) := by
  obtain ⟨e, he⟩ := PLAnnularStrip.exists_annulus_homeomorph
    (L := (2 : ℝ)) (d := 0) (by norm_num) (by norm_num) (by norm_num)
  let i : C8 ≃ₜ C8 × Icc (-(0 : ℝ)) 0 :=
    { toFun := fun z => (z, ⟨0, by norm_num⟩)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨z, t⟩
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          have ht := t.property
          simp only [neg_zero, mem_Icc] at ht
          exact le_antisymm ht.1 ht.2
      continuous_toFun := continuous_id.prodMk continuous_const
      continuous_invFun := continuous_fst }
  have himage : squareCenter '' PLAnnularStrip.squareAnnulus 2 0 = Q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (squareCenter_mem x).mpr hx
    · intro hy
      refine ⟨squareCenter.symm y, ?_, squareCenter.apply_symm_apply y⟩
      exact (squareCenter_mem _).mp (by simpa using hy)
  let a := (squareCenter.toHomeomorph.image
    (PLAnnularStrip.squareAnnulus 2 0)).trans (Homeomorph.setCongr himage)
  refine ⟨i.trans (e.trans a), ?_⟩
  intro z
  change squareCenter (e (i z)) = _
  rw [he]
  rfl




noncomputable def squareCircle : C8 ≃ₜ Q :=
  Classical.choose exists_squareCircle



theorem squareCircle_apply (z : C8) :
    (squareCircle z : V2) =
      squareCenter (PLAnnularStrip.annulusMap 2 (by norm_num) (z, 0)) :=
  Classical.choose_spec exists_squareCircle z




theorem finitePiecewiseAffineOn_squareCircle_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} {S : Set E} (hf : FinitePiecewiseAffineOn f S) :
    FinitePiecewiseAffineOn
      (fun x => (squareCircle ((f x : ℝ) : C8) : V2)) S := by
  have hzero : FinitePiecewiseAffineOn (fun _ : E => (0 : ℝ)) S := by
    obtain ⟨K, hK, hKS, _⟩ := hf
    exact ⟨K, hK, hKS, K.affineOnFaces_affine (ContinuousAffineMap.const ℝ E 0)⟩
  have hPL := PLAnnularStrip.locallyPiecewiseAffineOn_annulusMap_lift
    (L := (2 : ℝ)) (d := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  have hcomp := hPL.comp_finitePiecewiseAffineOn (hf.prod_mk hzero)
    (by intro x hx; exact ⟨mem_univ _, by norm_num⟩)
  exact (hcomp.postcomp squareCenter.toContinuousAffineMap).congr
    (fun x _ => (squareCircle_apply _).symm)

end PoincareConjecture.M76.HamiltonIndexOne
