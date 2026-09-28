import PoincareConjecture.Proofs.M76.PrimeReduction.Mathlib.NormalizedEdgeCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Segment








set_option autoImplicit false
open Set

namespace PoincareConjecture.M76
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_affine_collar_edge_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) {u v p : E} (hgap : A v - A u ≠ 0)
    (hp : p ∈ affineSpan ℝ ({u, v} : Set E)) (hpzero : A p = 0) :
    ∃ F : C3 ≃ᴬ[ℝ] E, F 0 = p ∧
      (∀ z, A (F z) = z.2) ∧ F.symm u = ((0, 0), A u) ∧
      F.symm v = ((0, 0), A v) := by
  let ell : E →ₗ[ℝ] ℝ := A.linear
  let d : E := (A v - A u)⁻¹ • (v - u)
  have hd : ell d = 1 := by
    change A.linear ((A v - A u)⁻¹ • (v - u)) = 1
    have hsub : A.linear (v - u) = A v - A u := A.linearMap_vsub v u
    rw [map_smul, hsub]
    exact inv_mul_cancel₀ hgap
  have hell : ell ≠ 0 := by
    intro h
    have h0 : ell d = 0 := by rw [h]; rfl
    linarith
  have hker : Module.finrank ℝ ell.ker = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    omega
  let e : (ℝ × ℝ) ≃ₗ[ℝ] ell.ker := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_prod, hker])
  let L : C3 →ₗ[ℝ] E :=
    (ell.ker.subtype.comp e.toLinearMap).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ) +
      (LinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight d
  have hL (z : C3) : L z = (e z.1 : E) + z.2 • d := rfl
  have hheight (z : C3) : ell (L z) = z.2 := by
    have he0 : ell (e z.1 : E) = 0 := (e z.1).property
    rw [hL, map_add, map_smul, he0, hd]
    simp
  have hi : Function.Injective L := by
    intro x y hxy
    have hlast : x.2 = y.2 := (hheight x).symm.trans ((congrArg ell hxy).trans (hheight y))
    have hfirst : (e x.1 : E) = e y.1 := by
      have heq : (e x.1 : E) + y.2 • d = (e y.1 : E) + y.2 • d := by
        simpa only [hL, hlast] using hxy
      exact add_right_cancel heq
    exact Prod.ext (e.injective (Subtype.ext hfirst)) hlast
  have hsurj : Function.Surjective L := by
    intro x
    let y : ell.ker := ⟨x - ell x • d, by
      change ell (x - ell x • d) = 0
      rw [map_sub, map_smul, hd]
      simp⟩
    refine ⟨(e.symm y, ell x), ?_⟩
    rw [hL, e.apply_symm_apply]
    change x - ell x • d + ell x • d = x
    abel
  let B := (LinearEquiv.ofBijective L ⟨hi, hsurj⟩).toContinuousLinearEquiv
  let F := B.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ E p)
  have hF (z : C3) : F z = L z + p := add_comm _ _
  have hFp : F 0 = p := by rw [hF, map_zero, zero_add]
  have hFpheight (z : C3) : A (F z) = z.2 := by
    rw [hF]
    change A (L z +ᵥ p) = z.2
    rw [A.map_vadd, hpzero]
    exact (add_zero _).trans (hheight z)
  obtain ⟨t, htp⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
  have hvalue : u + t • (v - u) = p := by
    rw [AffineMap.lineMap_apply_module] at htp
    calc
      u + t • (v - u) = (1 - t) • u + t • v := by module
      _ = p := htp
  have htvalue : t * (A v - A u) = -A u := by
    have h := congrArg A htp
    rw [A.apply_lineMap, AffineMap.lineMap_apply_module, hpzero] at h
    simp only [smul_eq_mul] at h
    nlinarith
  have htdiv : t = -A u * (A v - A u)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hgap).mpr htvalue
  have haxis (r : ℝ) : F ((0, 0), r) = r • d + p := by
    rw [hF, hL]
    change (e (0 : ℝ × ℝ) : E) + r • d + p = r • d + p
    rw [map_zero]
    change (0 : E) + r • d + p = r • d + p
    rw [zero_add]
  have haxisu : F ((0, 0), A u) = u := by
    rw [haxis, ← hvalue, htdiv]
    dsimp only [d]
    module
  have haxisv : F ((0, 0), A v) = v := by
    calc
      F ((0, 0), A v) = F ((0, 0), A u) + (A v - A u) • d := by
        rw [haxis, haxis]
        module
      _ = u + (v - u) := by
        rw [haxisu]
        dsimp only [d]
        rw [smul_smul, mul_inv_cancel₀ hgap, one_smul]
      _ = v := by abel
  exact ⟨F, hFp, hFpheight,
    (congrArg F.symm haxisu).symm.trans (F.symm_apply_apply _),
    (congrArg F.symm haxisv).symm.trans (F.symm_apply_apply _)⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_affine_plane_edge_crossing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᴬ[ℝ] ℝ) {u v p : E} (hu : A u < 0) (hv : 0 < A v)
    (hp : p ∈ segment ℝ u v) (hpzero : A p = 0)
    {O : Set E} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (F : C3 ≃ᴬ[ℝ] E) (V : Set E),
      IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧ F 0 = p ∧
      (∀ z, A (F z) = z.2) ∧
      ∀ z, F z ∈ V → (F z ∈ segment ℝ u v ↔ z.1 = 0) := by
  have hgap : A v - A u ≠ 0 := (sub_pos.mpr (hu.trans hv)).ne'
  obtain ⟨F, hF, hheight, hFu, hFv⟩ := exists_affine_collar_edge_coordinates hdim
    A.toAffineMap hgap (convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hp)) hpzero
  change (∀ z, A (F z) = z.2) at hheight
  change F.symm u = ((0, 0), A u) at hFu
  change F.symm v = ((0, 0), A v) at hFv
  let V := O ∩ A ⁻¹' Ioo (A u) (A v)
  refine ⟨F, V, hO.inter (isOpen_Ioo.preimage A.continuous),
    ⟨hpO, by simpa only [mem_preimage, mem_Ioo, hpzero] using And.intro hu hv⟩,
    inter_subset_left, hF, hheight, ?_⟩
  intro z hz
  have hmem : F z ∈ segment ℝ u v ↔
      z ∈ segment ℝ (((0, 0), A u) : C3) ((0, 0), A v) := by
    have heq : F.symm '' segment ℝ u v = segment ℝ (F.symm u) (F.symm v) :=
      image_segment ℝ F.symm.toAffineEquiv.toAffineMap u v
    rw [← hFu, ← hFv, ← heq]
    constructor
    · intro h
      exact ⟨F z, h, F.symm_apply_apply z⟩
    · rintro ⟨y, hy, hyz⟩
      have heq : y = F z := by
        simpa only [F.apply_symm_apply] using congrArg F hyz
      exact heq ▸ hy
  rw [hmem]
  constructor
  · intro hzseg
    obtain ⟨t, _, htz⟩ := (segment_eq_image_lineMap ℝ _ _).subset hzseg
    have h := congrArg Prod.fst htz
    change z.1 = (0, 0)
    simpa [AffineMap.lineMap_apply_module] using h.symm
  · intro hzfirst
    let axis : ℝ →ᵃ[ℝ] C3 := (LinearMap.inr ℝ (ℝ × ℝ) ℝ).toAffineMap
    have hlast : z.2 ∈ segment ℝ (A u) (A v) := by
      rw [segment_eq_Icc (hu.trans hv).le]
      have hh : A u < z.2 ∧ z.2 < A v := by
        have hh : A u < A (F z) ∧ A (F z) < A v := hz.2
        simpa only [hheight] using hh
      exact ⟨hh.1.le, hh.2.le⟩
    have hh := mem_image_of_mem axis hlast
    rw [image_segment ℝ axis] at hh
    have hzaxis : axis z.2 = z := Prod.ext hzfirst.symm rfl
    rw [hzaxis] at hh
    exact hh

end PoincareConjecture.M76
