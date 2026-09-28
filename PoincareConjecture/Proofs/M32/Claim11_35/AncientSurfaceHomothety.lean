import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Analysis.Calculus.MeanValue

















set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M32

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]




theorem roundSurface_scalarCurvature_eq_one_div_one_sub
    (hM04 : RicciFlowCurvatureTheory.{u}) (A : RicciFlow 2 C (Iic 0))
    (hround : ∀ t ≤ 0,
      ConstantPositiveSectionalCurvature (A.metric t) (A.connection t))
    (p : C) (hzero : (A.connection 0).scalarCurvature p = 1) :
    ∀ t ≤ 0, ∀ x : C, (A.connection t).scalarCurvature x = 1 / (1 - t) := by
  intro t ht x
  let R : ℝ → ℝ := fun s => (A.connection s).scalarCurvature x
  have hpositive (s : ℝ) (hs : s ≤ 0) : 0 < R s := by
    obtain ⟨r, hr, heq⟩ :=
      (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp (hround s hs)
    change 0 < (A.connection s).scalarCurvature x
    rw [heq x]
    exact hr
  have hinit : R 0 = 1 := by
    obtain ⟨r, _, heq⟩ :=
      (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp (hround 0 le_rfl)
    exact (heq x).trans ((heq p).symm.trans hzero)
  have hderiv (s : ℝ) (hs : s ∈ Iic 0) :
      HasDerivWithinAt R (R s ^ 2) (Iic 0) s := by
    obtain ⟨r, _, heq⟩ :=
      (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp (hround s hs)
    have hconst : (A.connection s).scalarCurvature = fun _ => r := funext heq
    have hlap : (A.connection s).laplacian (A.connection s).scalarCurvature x = 0 := by
      rw [hconst]
      simp only [LeviCivitaData.laplacian, LeviCivitaData.hessian,
        LeviCivitaData.hessianOnFields, mvfderiv_const,
        zero_apply, sub_self, Finset.sum_const_zero]
    have h := hM04.scalar_evolution 2 C (Iic 0) A s hs x
    rw [hlap, (A.connection s).ricciNormSq_eq_half_scalarCurvature_sq] at h
    convert h using 1
    dsimp [R]
    ring
  have hsum (s : ℝ) (hs : s ∈ Iic 0) :
      HasDerivWithinAt (fun z => (R z)⁻¹ + z) 0 (Iic 0) s := by
    have hinv : HasDerivWithinAt (fun z => (R z)⁻¹) (-1) (Iic 0) s := by
      exact ((hderiv s hs).inv (hpositive s hs).ne').congr_deriv
        (by simp [(hpositive s hs).ne'])
    have hid : HasDerivWithinAt (fun z : ℝ => z) 1 (Iic 0) s :=
      hasDerivWithinAt_id _ _
    exact (hinv.add hid).congr_deriv (by ring)
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := (0 : ℝ)) hsum (fun _ _ => by simp) (convex_Iic (0 : ℝ))
    (show (0 : ℝ) ∈ Iic 0 by simp) ht
  have heq : (R t)⁻¹ + t = (R 0)⁻¹ + 0 :=
    sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _)))
  have hinv : (R t)⁻¹ = 1 - t := by
    rw [hinit] at heq
    norm_num at heq
    linarith
  have h := congrArg Inv.inv hinv
  simpa only [inv_inv, one_div] using h




theorem roundSurface_inner_eq_one_sub_mul
    (A : RicciFlow 2 C (Iic 0))
    (hscalar : ∀ t ≤ 0, ∀ x : C,
      (A.connection t).scalarCurvature x = 1 / (1 - t)) :
    ∀ t ≤ 0, ∀ x : C, ∀ u v : TangentSpace (𝓡 2) x,
      (A.metric t).inner x u v = (1 - t) * (A.metric 0).inner x u v := by
  intro t ht x u v
  let f : ℝ → ℝ := fun s => (A.metric s).inner x u v
  have hden (s : ℝ) (hs : s ≤ 0) : 0 < 1 - s := by linarith
  have hderiv (s : ℝ) (hs : s ∈ Iic 0) :
      HasDerivWithinAt f (-f s / (1 - s)) (Iic 0) s := by
    have h := A.equation s hs x u v
    rw [(A.connection s).ricci_eq_half_scalarCurvature_mul_inner, hscalar s hs] at h
    convert h using 1
    dsimp [f]
    ring
  have hquot (s : ℝ) (hs : s ∈ Iic 0) :
      HasDerivWithinAt (fun z => f z / (1 - z)) 0 (Iic 0) s := by
    have hd : HasDerivWithinAt (fun z : ℝ => 1 - z) (-1) (Iic 0) s := by
      have hid : HasDerivWithinAt (fun z : ℝ => z) 1 (Iic 0) s :=
        hasDerivWithinAt_id _ _
      exact hid.const_sub 1
    exact ((hderiv s hs).div hd (hden s hs).ne').congr_deriv
      (by field_simp [(hden s hs).ne']; ring)
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := (0 : ℝ)) hquot (fun _ _ => by simp) (convex_Iic (0 : ℝ))
    (show (0 : ℝ) ∈ Iic 0 by simp) ht
  have heq : f t / (1 - t) = f 0 / (1 - 0) :=
    sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _)))
  have heq' : f t / (1 - t) = f 0 := by
    simpa only [sub_zero, div_one] using heq
  have h := (div_eq_iff (hden t ht).ne').mp heq'
  simpa only [mul_comm] using h

end PoincareConjecture.M32
