import PoincareConjecture.Proofs.M76.Mathlib.RadialTriangleIncidence
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Order.DenselyOrdered












set_option autoImplicit false

open Set AffineMap CoordinateHalfBoxes

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem le_of_inter_subset_open (P Q : AffineSubspace ℝ E)
    {U : Set E} (hU : IsOpen U) {a : E} (haP : a ∈ P) (haU : a ∈ U)
    (hPQ : (P : Set E) ∩ U ⊆ Q) : P ≤ Q := by
  have haQ : a ∈ Q := hPQ ⟨haP, haU⟩
  intro x hx
  let l : ℝ → E := lineMap a x
  have hl : Continuous l := (ContinuousAffineMap.lineMap a x).continuous
  have hV : IsOpen (l ⁻¹' U) := hU.preimage hl
  have hzero : (0 : ℝ) ∈ l ⁻¹' U := by
    simpa only [l, mem_preimage, lineMap_apply_zero] using haU
  have hclosure : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨t, htU, ht⟩ := mem_closure_iff.mp hclosure (l ⁻¹' U) hV hzero
  have htQ : lineMap a x t ∈ Q := hPQ ⟨lineMap_mem t haP hx, htU⟩
  have hxQ := lineMap_mem t⁻¹ haQ htQ
  simpa only [lineMap_lineMap_right, inv_mul_cancel₀ ht.1.ne', lineMap_apply_one] using hxQ




theorem eq_of_inter_eq_open (P Q : AffineSubspace ℝ E)
    {U : Set E} (hU : IsOpen U) {a : E} (haP : a ∈ P) (haU : a ∈ U)
    (hPQ : (P : Set E) ∩ U = (Q : Set E) ∩ U) : P = Q := by
  have haQ : a ∈ Q := (hPQ.subset ⟨haP, haU⟩).1
  exact le_antisymm
    (P.le_of_inter_subset_open Q hU haP haU (hPQ.subset.trans inter_subset_left))
    (Q.le_of_inter_subset_open P hU haQ haU (hPQ.symm.subset.trans inter_subset_left))

end AffineSubspace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem mem_triangle_affineSpan_iff_last_eq_zero_of_cut_box
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hf0 : f 0 = a)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : ∀ x ∈ box r, f x ∈ K.space ↔ x.2 = 0)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hlast : ∀ x : (ℝ × ℝ) × ℝ, (e (f x)).2 = x.2) :
    ∀ x : E, x ∈ affineSpan ℝ (s : Set E) ↔ (e x).2 = 0 := by
  let P := affineSpan ℝ (s : Set E)
  let Q := ((LinearMap.snd ℝ (ℝ × ℝ) ℝ).comp e.toLinearMap).ker.toAffineSubspace
  have hQ (x : E) : x ∈ Q ↔ (e x).2 = 0 := Iff.rfl
  have haP : a ∈ P := convexHull_subset_affineSpan _ (intrinsicInterior_subset ha)
  obtain ⟨U, hU, haU, hKU⟩ :=
    K.exists_open_eq_affineSpan_of_triangle_interior hK hbound hs hcard ha
  have habox : a ∈ interior (f '' box r) := by
    change a ∈ interior (f.toHomeomorph '' box r)
    rw [← f.toHomeomorph.image_interior]
    exact ⟨0, zero_mem_interior_box hr, hf0⟩
  let W := U ∩ interior (f '' box r)
  have hW : IsOpen W := hU.inter isOpen_interior
  have haW : a ∈ W := ⟨haU, habox⟩
  have hlocal (x : E) (hxW : x ∈ W) : x ∈ P ↔ x ∈ Q := by
    have hxbox : f.symm x ∈ box r := by
      obtain ⟨y, hy, hfy⟩ := interior_subset hxW.2
      have heq : f.symm x = y := by rw [← hfy, f.symm_apply_apply]
      rwa [heq]
    have hPK : x ∈ P ↔ x ∈ K.space :=
      ⟨fun hx => (hKU.symm.subset ⟨hx, hxW.1⟩).1,
        fun hx => (hKU.subset ⟨hx, hxW.1⟩).1⟩
    have hplane : x ∈ K.space ↔ (f.symm x).2 = 0 := by
      simpa only [f.apply_symm_apply] using hcarrier (f.symm x) hxbox
    have hlastx : (e x).2 = (f.symm x).2 := by
      simpa only [f.apply_symm_apply] using hlast (f.symm x)
    rw [hQ, hlastx]
    exact hPK.trans hplane
  have hPQ : P = Q := by
    apply P.eq_of_inter_eq_open Q hW haP haW
    ext x
    constructor
    · rintro ⟨hx, hxW⟩
      exact ⟨(hlocal x hxW).mp hx, hxW⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨(hlocal x hxW).mpr hx, hxW⟩
  intro x
  change x ∈ P ↔ (e x).2 = 0
  rw [hPQ]
  exact hQ x

variable [DecidableEq E]





theorem exists_open_surface_eq_last_at_radial_frontier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hf0 : f 0 = a)
    {r : ℝ} (hr : 0 < r)
    (hcarrier : ∀ x ∈ box r, f x ∈ K.space ↔ x.2 = 0)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hlast : ∀ x : (ℝ × ℝ) × ℝ, (e (f x)).2 = x.2)
    {C : Set E} (hC : IsClosed C) (hlink : Disjoint C (K.link 0).space)
    (hpC : p ∈ frontier C) (hpstar : p ∈ (K.closedStar 0).space)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hpa : p = ρ • a) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, x ∈ K.space ↔ (e x).2 = 0 := by
  have hplane := K.mem_triangle_affineSpan_iff_last_eq_zero_of_cut_box
    hK hbound hs hcard ha f hf0 hr hcarrier e hlast
  obtain ⟨U, hU, hpU, hKU⟩ :=
    K.exists_open_eq_triangle_plane_at_radial_frontier
      hK hbound hs hcard ha hC hlink hpC hpstar hρ hpa
  refine ⟨U, hU, hpU, ?_⟩
  intro x hxU
  exact (show x ∈ K.space ↔ x ∈ affineSpan ℝ (s : Set E) from
    ⟨fun hx => (hKU.subset ⟨hx, hxU⟩).1,
      fun hx => (hKU.symm.subset ⟨hx, hxU⟩).1⟩).trans (hplane x)

end Geometry.SimplicialComplex
