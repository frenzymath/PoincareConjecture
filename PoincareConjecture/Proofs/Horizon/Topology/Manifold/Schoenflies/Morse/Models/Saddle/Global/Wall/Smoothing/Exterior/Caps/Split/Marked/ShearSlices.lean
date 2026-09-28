import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.QuadraticPatch.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.Shear

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

open Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
local notation "IT" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

def sphereLatitude (t : Real) (q : S1) : E3 :=
  vector (Real.sqrt (1 - t ^ 2) * (q : E2) 0)
    (Real.sqrt (1 - t ^ 2) * (q : E2) 1) t

@[simp] theorem sphereLatitude_height (t : Real) (q : S1) : sphereLatitude t q 2 = t := rfl

theorem sphereLatitude_radicand_pos {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) :
    0 < 1 - t ^ 2 := by
  nlinarith [ht.1, ht.2]

theorem sphereLatitude_mem_sphere {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) (q : S1) :
    sphereLatitude t q ∈ sphere (0 : E3) 1 := by
  have hq : (q : E2) 0 ^ 2 + (q : E2) 1 ^ 2 = 1 := by
    have he := EuclideanSpace.norm_sq_eq (q : E2)
    simpa only [norm_eq_of_mem_sphere, one_pow, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using he.symm
  have hn : ‖sphereLatitude t q‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, sphereLatitude,
      vector_zero, vector_one, vector_two, mul_pow, Real.sq_sqrt (sphereLatitude_radicand_pos ht).le]
    nlinarith [congrArg (fun r : Real => (1 - t ^ 2) * r) hq]
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (sphereLatitude t q)]

theorem contMDiffOn_sphereLatitude :
    ContMDiffOn IT (𝓡 3) ∞ (fun z : Real × S1 => sphereLatitude z.1 z.2)
      (Ioo (-1 : Real) 1 ×ˢ univ) := by
  let f : Real × E2 → E3 := fun z =>
    vector (Real.sqrt (1 - z.1 ^ 2) * z.2 0) (Real.sqrt (1 - z.1 ^ 2) * z.2 1) z.1
  have hr : ContDiffOn Real ∞ (fun z : Real × E2 => Real.sqrt (1 - z.1 ^ 2))
      (Ioo (-1 : Real) 1 ×ˢ univ) :=
    ((contDiff_const.sub (contDiff_fst.pow 2)).contDiffOn.sqrt
      (fun z hz => (sphereLatitude_radicand_pos hz.1).ne'))
  have hf : ContDiffOn Real ∞ f (Ioo (-1 : Real) 1 ×ˢ univ) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    fin_cases i
    · exact hr.mul (by fun_prop)
    · exact hr.mul (by fun_prop)
    · exact contDiff_fst.contDiffOn
  have hp : ContMDiff IT 𝓘(Real, Real × E2) ∞
      (fun z : Real × S1 => (z.1, (z.2 : E2))) := by
    exact contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd)
  exact hf.contMDiffOn.comp hp.contMDiffOn (fun _ hz => ⟨hz.1, mem_univ _⟩)

theorem sphereLatitude_isSmoothEmbedding {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ (sphereLatitude t) := by
  have hr : Real.sqrt (1 - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (sphereLatitude_radicand_pos ht)).ne'
  let L : E3 → E2 := fun y => (Real.sqrt (1 - t ^ 2))⁻¹ • horizontal y
  have hL : ContMDiff (𝓡 3) (𝓡 2) ∞ L :=
    ((contDiff_const (c := (Real.sqrt (1 - t ^ 2))⁻¹)).smul horizontal_contDiff).contMDiff
  have hleft : L ∘ sphereLatitude t = (fun q : S1 => (q : E2)) := by
    funext q
    ext i
    fin_cases i <;> simp [L, sphereLatitude, horizontal, vector, hr]
  have hlat : ContMDiff (𝓡 1) (𝓡 3) ∞ (sphereLatitude t) := by
    intro q
    exact (contMDiffOn_sphereLatitude.contMDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ q⟩)).comp q
        ((contMDiff_const.prodMk contMDiff_id) q)
  apply isSmoothEmbedding_of_injective_mfderiv hlat
  · intro q q' hqq'
    apply Subtype.val_injective
    have he := congrArg L hqq'
    simpa only [← comp_apply (f := L), hleft] using he
  · intro q
    have hchain := mfderiv_comp q (hL.mdifferentiable (by simp) _)
      (hlat.mdifferentiable (by simp) q)
    rw [hleft] at hchain
    intro x y hxy
    apply injective_mvfderiv_subtypeVal_sphere (n := 1) q
    have he := congrArg (mfderiv (𝓡 3) (𝓡 2) L (sphereLatitude t q)) hxy
    change ((mfderiv (𝓡 3) (𝓡 2) L (sphereLatitude t q)).comp
      (mfderiv (𝓡 1) (𝓡 3) (sphereLatitude t) q)) x =
        ((mfderiv (𝓡 3) (𝓡 2) L (sphereLatitude t q)).comp
          (mfderiv (𝓡 1) (𝓡 3) (sphereLatitude t) q)) y at he
    rw [← hchain] at he
    exact he

theorem range_sphereLatitude {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) :
    range (sphereLatitude t) = sphere (0 : E3) 1 ∩ {y | y 2 = t} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨sphereLatitude_mem_sphere ht q, rfl⟩
  · rintro ⟨hy, hyt⟩
    change y 2 = t at hyt
    let r := Real.sqrt (1 - t ^ 2)
    have hr : 0 < r := Real.sqrt_pos.mpr (sphereLatitude_radicand_pos ht)
    have hrsq : r ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (sphereLatitude_radicand_pos ht).le
    have hyq : y 0 ^ 2 + y 1 ^ 2 = r ^ 2 := by
      have he := EuclideanSpace.norm_sq_eq y
      rw [mem_sphere_zero_iff_norm.mp hy] at he
      simp only [one_pow, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hyt] at he
      linarith
    let q : S1 := ⟨r⁻¹ • horizontal y, by
      have hn : ‖r⁻¹ • horizontal y‖ ^ 2 = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), mul_pow,
          norm_sq_two, show horizontal y 0 = y 0 from rfl,
          show horizontal y 1 = y 1 from rfl, hyq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
      rw [mem_sphere_zero_iff_norm]
      nlinarith [norm_nonneg (r⁻¹ • horizontal y)]⟩
    refine ⟨q, ?_⟩
    ext i
    fin_cases i
    · change r * (r⁻¹ * y 0) = y 0
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    · change r * (r⁻¹ * y 1) = y 1
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    · exact hyt.symm

def tangentFlatShearSlice (z : Real × S1) : E3 :=
  tangentFlatShear (sphereLatitude z.1 z.2)

@[simp] theorem tangentFlatShearSlice_height (t : Real) (q : S1) :
    tangentFlatShearSlice (t, q) 2 = t := by
  simp only [tangentFlatShearSlice, tangentFlatShear_two, sphereLatitude_height]

theorem contMDiffOn_tangentFlatShearSlice :
    ContMDiffOn IT (𝓡 3) ∞ tangentFlatShearSlice (Ioo (-1 : Real) 1 ×ˢ univ) :=
  tangentFlatShear.contMDiff.comp_contMDiffOn contMDiffOn_sphereLatitude

theorem tangentFlatShearSlice_isSmoothEmbedding {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞
      (fun q => tangentFlatShearSlice (t, q)) := by
  have hlat := sphereLatitude_isSmoothEmbedding ht
  apply isSmoothEmbedding_of_injective_mfderiv
    (tangentFlatShear.contMDiff.comp hlat.contMDiff)
    (tangentFlatShear.injective.comp hlat.isEmbedding.injective)
  intro q
  change Injective (mfderiv (𝓡 1) (𝓡 3) (tangentFlatShear ∘ sphereLatitude t) q)
  rw [mfderiv_comp q (tangentFlatShear.contMDiff.mdifferentiable (by simp) _)
    (hlat.contMDiff.mdifferentiable (by simp) _)]
  exact (tangentFlatShear.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
    ((hlat.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp))

theorem range_tangentFlatShearSlice {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) :
    range (fun q => tangentFlatShearSlice (t, q)) =
      (tangentFlatShear '' sphere (0 : E3) 1) ∩ {y | y 2 = t} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨sphereLatitude t q, sphereLatitude_mem_sphere ht q, rfl⟩,
      tangentFlatShearSlice_height t q⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
    have hh : x 2 = t := by
      change tangentFlatShear x 2 = t at hxt
      simpa only [tangentFlatShear_two] using hxt
    obtain ⟨q, hq⟩ := (range_sphereLatitude ht).symm ▸
      (show x ∈ sphere (0 : E3) 1 ∩ {y | y 2 = t} from ⟨hx, hh⟩)
    exact ⟨q, congrArg tangentFlatShear hq⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
