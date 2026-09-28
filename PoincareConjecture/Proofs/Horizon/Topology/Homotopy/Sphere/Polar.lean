import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open scoped Manifold ContDiff
open Metric Set

noncomputable section

namespace Poincare.Topology

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

abbrev PolarSphere (n : ℕ) := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

def spherePolarVector {n : ℕ} (x : PolarSphere n × ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  WithLp.toLp 2 (Fin.cons x.2 x.1.val)

theorem spherePolarVector_norm_sq {n : ℕ} (x : PolarSphere n × ℝ) :
    ‖spherePolarVector x‖ ^ 2 = 1 + x.2 ^ 2 := by
  have hx : ‖x.1.val‖ = 1 := by simp
  have hs : ∑ i, (x.1.val i) ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq x.1.val
    rw [hx] at h
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using h.symm
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [spherePolarVector, WithLp.ofLp_toLp, Fin.cons_zero, Fin.cons_succ,
    Real.norm_eq_abs, sq_abs]
  rw [hs]
  ring

theorem spherePolarVector_norm_pos {n : ℕ} (x : PolarSphere n × ℝ) :
    0 < ‖spherePolarVector x‖ := by
  have h := spherePolarVector_norm_sq x
  have := sq_nonneg x.2
  nlinarith [norm_nonneg (spherePolarVector x)]

def spherePolarMap {n : ℕ} (x : PolarSphere n × ℝ) : PolarSphere (n + 1) :=
  ⟨‖spherePolarVector x‖⁻¹ • spherePolarVector x, by
    simp only [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt (spherePolarVector_norm_pos x))⟩

theorem spherePolarVector_neg {n : ℕ} (x : PolarSphere n × ℝ) :
    spherePolarVector (-x.1, -x.2) = -spherePolarVector x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem spherePolarMap_neg {n : ℕ} (x : PolarSphere n × ℝ) :
    spherePolarMap (-x.1, -x.2) = -spherePolarMap x := by
  apply Subtype.ext
  change ‖spherePolarVector (-x.1, -x.2)‖⁻¹ • spherePolarVector (-x.1, -x.2) = _
  rw [spherePolarVector_neg, norm_neg, smul_neg]
  rfl

def spherePolarTail {n : ℕ} (x : PolarSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => x.val i.succ)

theorem continuous_spherePolarVector {n : ℕ} :
    Continuous (spherePolarVector : PolarSphere n × ℝ → _) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_snd
  · exact (PiLp.continuous_apply 2 _ j).comp
      (continuous_subtype_val.comp continuous_fst)

theorem continuous_spherePolarTail {n : ℕ} :
    Continuous (spherePolarTail : PolarSphere (n + 1) → _) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i =>
    (PiLp.continuous_apply 2 _ i.succ).comp continuous_subtype_val

def spherePolarDomain (n : ℕ) : TopologicalSpace.Opens (PolarSphere (n + 1)) :=
  ⟨{x | spherePolarTail x ≠ 0},
    isOpen_ne.preimage continuous_spherePolarTail⟩

theorem spherePolarTail_map {n : ℕ} (x : PolarSphere n × ℝ) :
    spherePolarTail (spherePolarMap x) = ‖spherePolarVector x‖⁻¹ • x.1.val := by
  ext i
  rfl

theorem spherePolarTail_map_norm {n : ℕ} (x : PolarSphere n × ℝ) :
    ‖spherePolarTail (spherePolarMap x)‖ = ‖spherePolarVector x‖⁻¹ := by
  rw [spherePolarTail_map, norm_smul, norm_inv, norm_norm]
  have hx : ‖x.1.val‖ = 1 := by simp
  rw [hx, mul_one]

theorem spherePolarMap_mem {n : ℕ} (x : PolarSphere n × ℝ) :
    spherePolarMap x ∈ spherePolarDomain n := by
  intro h
  have := spherePolarTail_map_norm x
  rw [h, norm_zero] at this
  exact (inv_ne_zero (ne_of_gt (spherePolarVector_norm_pos x))) this.symm

def spherePolarInverse {n : ℕ} (x : spherePolarDomain n) : PolarSphere n × ℝ :=
  (⟨‖spherePolarTail x.val‖⁻¹ • spherePolarTail x.val, by
    simp only [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.property)⟩,
    x.val.val 0 / ‖spherePolarTail x.val‖)

theorem spherePolar_left_inv {n : ℕ} (x : PolarSphere n × ℝ) :
    spherePolarInverse ⟨spherePolarMap x, spherePolarMap_mem x⟩ = x := by
  have h := ne_of_gt (spherePolarVector_norm_pos x)
  apply Prod.ext
  · apply Subtype.ext
    change ‖spherePolarTail (spherePolarMap x)‖⁻¹ •
      spherePolarTail (spherePolarMap x) = x.1.val
    rw [spherePolarTail_map_norm, spherePolarTail_map, inv_inv, smul_smul,
      mul_inv_cancel₀ h, one_smul]
  · change (‖spherePolarVector x‖⁻¹ * x.2) /
      ‖spherePolarTail (spherePolarMap x)‖ = x.2
    rw [spherePolarTail_map_norm]
    field_simp

theorem spherePolarVector_inverse {n : ℕ} (x : spherePolarDomain n) :
    spherePolarVector (spherePolarInverse x) =
      ‖spherePolarTail x.val‖⁻¹ • x.val.val := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change x.val.val 0 / ‖spherePolarTail x.val‖ =
      ‖spherePolarTail x.val‖⁻¹ * x.val.val 0
    exact div_eq_inv_mul _ _
  · rfl

theorem spherePolar_right_inv {n : ℕ} (x : spherePolarDomain n) :
    spherePolarMap (spherePolarInverse x) = x.val := by
  have hx : ‖x.val.val‖ = 1 := by simp
  have h := norm_ne_zero_iff.mpr x.property
  apply Subtype.ext
  change ‖spherePolarVector (spherePolarInverse x)‖⁻¹ •
      spherePolarVector (spherePolarInverse x) = x.val.val
  rw [spherePolarVector_inverse, norm_smul, norm_inv, norm_norm, hx, mul_one,
    inv_inv, smul_smul, mul_inv_cancel₀ h, one_smul]

def spherePolarHomeomorph (n : ℕ) : (PolarSphere n × ℝ) ≃ₜ spherePolarDomain n where
  toFun x := ⟨spherePolarMap x, spherePolarMap_mem x⟩
  invFun := spherePolarInverse
  left_inv := spherePolar_left_inv
  right_inv x := Subtype.ext (spherePolar_right_inv x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_spherePolarVector.norm.inv₀
      (fun x => ne_of_gt (spherePolarVector_norm_pos x))).smul
      continuous_spherePolarVector
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_spherePolarTail.comp continuous_subtype_val).norm.inv₀
        (fun x => norm_ne_zero_iff.mpr x.property)).smul
        (continuous_spherePolarTail.comp continuous_subtype_val)
    · exact ((PiLp.continuous_apply 2 _ 0).comp
        (continuous_subtype_val.comp continuous_subtype_val)).div
        ((continuous_spherePolarTail.comp continuous_subtype_val).norm)
        (fun x => norm_ne_zero_iff.mpr x.property)

theorem contMDiff_spherePolarVector {n : ℕ} :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 2)) ∞
      (spherePolarVector : PolarSphere n × ℝ → _) := by
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm.contDiff.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contMDiff_snd
  · have h : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x : PolarSphere n => x.val j) :=
      (ContinuousLinearMap.proj j).contMDiff.comp
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).contDiff.contMDiff.comp
        (contMDiff_coe_sphere (n := n)))
    exact h.comp contMDiff_fst

theorem contMDiff_spherePolarTail {n : ℕ} :
    ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (spherePolarTail : PolarSphere (n + 1) → _) := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.contDiff.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro i
  exact (ContinuousLinearMap.proj i.succ).contMDiff.comp
    ((EuclideanSpace.equiv (Fin (n + 2)) ℝ).contDiff.contMDiff.comp
      (contMDiff_coe_sphere (n := n + 1)))

theorem contMDiff_spherePolarMap {n : ℕ} :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞
      (spherePolarMap : PolarSphere n × ℝ → _) := by
  apply ContMDiff.codRestrict_sphere
  have hn : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun x : PolarSphere n × ℝ => ‖spherePolarVector x‖) := by
    intro x
    exact ((contDiffAt_norm ℝ (norm_ne_zero_iff.mp
      (ne_of_gt (spherePolarVector_norm_pos x)))).contMDiffAt).comp x
      (contMDiff_spherePolarVector x)
  exact (hn.inv₀ (fun x => ne_of_gt (spherePolarVector_norm_pos x))).smul
    contMDiff_spherePolarVector

theorem contMDiff_spherePolarInverse {n : ℕ} :
    ContMDiff (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (spherePolarInverse : spherePolarDomain n → _) := by
  have ht : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (fun x : spherePolarDomain n => spherePolarTail x.val) :=
    contMDiff_spherePolarTail.comp contMDiff_subtype_val
  have hn : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
      (fun x : spherePolarDomain n => ‖spherePolarTail x.val‖) := by
    intro x
    exact ((contDiffAt_norm ℝ x.property).contMDiffAt).comp x (ht x)
  have hi := hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)
  apply ContMDiff.prodMk
  · exact (hi.smul ht).codRestrict_sphere _
  · have hz : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
        (fun x : spherePolarDomain n => x.val.val 0) :=
      (ContinuousLinearMap.proj 0).contMDiff.comp
        ((EuclideanSpace.equiv (Fin (n + 2)) ℝ).contDiff.contMDiff.comp
          ((contMDiff_coe_sphere (n := n + 1)).comp contMDiff_subtype_val))
    convert hi.smul hz using 1
    ext x
    simp [div_eq_mul_inv, mul_comm]

def spherePolarDiffeomorph (n : ℕ) :
    Diffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1))
      (PolarSphere n × ℝ) (spherePolarDomain n) ∞ where
  toEquiv := (spherePolarHomeomorph n).toEquiv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_spherePolarMap
  contMDiff_invFun := contMDiff_spherePolarInverse

def spherePolarPole (n : ℕ) : PolarSphere (n + 1) :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

theorem spherePolarTail_pole (n : ℕ) :
    spherePolarTail (spherePolarPole n) = 0 := by
  ext i
  simp [spherePolarTail, spherePolarPole]

theorem spherePolarTail_neg {n : ℕ} (x : PolarSphere (n + 1)) :
    spherePolarTail (-x) = -spherePolarTail x := by
  ext i
  rfl

theorem spherePolarTail_eq_zero_iff {n : ℕ} (x : PolarSphere (n + 1)) :
    spherePolarTail x = 0 ↔ x = spherePolarPole n ∨ x = -spherePolarPole n := by
  constructor
  · intro h
    have hi (i : Fin (n + 1)) : x.val i.succ = 0 := by
      exact congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y i) h
    have hn : ‖x.val‖ = 1 := by simp
    have hs := EuclideanSpace.norm_sq_eq x.val
    rw [hn, Fin.sum_univ_succ] at hs
    simp only [hi, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
      add_zero, Real.norm_eq_abs, sq_abs, one_pow] at hs
    have hz : x.val 0 = 1 ∨ x.val 0 = -1 := by
      exact sq_eq_one_iff.mp hs.symm
    rcases hz with hz | hz
    · left
      apply Subtype.ext
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [spherePolarPole] using hz
      · simpa [spherePolarPole] using hi j
    · right
      apply Subtype.ext
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [spherePolarPole] using hz
      · simpa [spherePolarPole] using hi j
  · rintro (rfl | rfl)
    · exact spherePolarTail_pole n
    · rw [spherePolarTail_neg, spherePolarTail_pole, neg_zero]

theorem spherePolarDomain_eq (n : ℕ) :
    (spherePolarDomain n : Set (PolarSphere (n + 1))) =
      {spherePolarPole n, -spherePolarPole n}ᶜ := by
  ext x
  simp [spherePolarDomain, spherePolarTail_eq_zero_iff]

def spherePolarInverseTotal (n : ℕ) (x : PolarSphere (n + 1)) :
    PolarSphere n × ℝ := by
  classical
  exact if hx : x ∈ spherePolarDomain n then spherePolarInverse ⟨x, hx⟩
    else (⟨EuclideanSpace.single 0 1, by simp⟩, 0)

@[simp]
theorem spherePolarInverseTotal_coe {n : ℕ} (x : spherePolarDomain n) :
    spherePolarInverseTotal n x.val = spherePolarInverse x := by
  simp [spherePolarInverseTotal, x.property]

def spherePolarPartialDiffeomorph (n : ℕ) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1))
      (PolarSphere n × ℝ) (PolarSphere (n + 1)) ∞ where
  toFun := spherePolarMap
  invFun := spherePolarInverseTotal n
  source := Set.univ
  target := spherePolarDomain n
  map_source' := fun {_} _ => spherePolarMap_mem _
  map_target' := fun {_} _ => Set.mem_univ _
  left_inv' := by
    intro x _
    simp only [spherePolarInverseTotal, dif_pos (spherePolarMap_mem x)]
    exact spherePolar_left_inv x
  right_inv' := by
    intro x hx
    change x ∈ spherePolarDomain n at hx
    simp only [spherePolarInverseTotal, dif_pos hx]
    exact spherePolar_right_inv ⟨x, hx⟩
  open_source := isOpen_univ
  open_target := (spherePolarDomain n).isOpen
  contMDiffOn_toFun := contMDiff_spherePolarMap.contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    have h : ContMDiffAt (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (spherePolarInverseTotal n ∘ Subtype.val) (⟨x, hx⟩ : spherePolarDomain n) := by
      simpa only [Function.comp_def, spherePolarInverseTotal_coe] using
        (contMDiff_spherePolarInverse (⟨x, hx⟩ : spherePolarDomain n))
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt

end Poincare.Topology
