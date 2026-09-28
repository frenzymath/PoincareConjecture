import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.Belt
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.SetImage
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.UnequalHeight

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

theorem exists_ambient_capped_cylinder_of_scales
    {v : E3} (hv : ‖v‖ = 1) (a b : Real) (hab : a ≤ b)
    (u w : Real) (hu : 0 < u) (hw : 0 < w)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A ''
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | 0 ≤ inner Real v (p : E3)})) ∪
        ((fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
          (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1)) ∪
        (liftPlaneDiffeomorph hv b w hw.ne' A ''
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | 0 ≤ inner Real v (p : E3)})) := by
  let C := heightCoordinates hv
  let graph : S2 → E3 := fun p => boundedCylinderRadius v p • (p : E3)
  let S : Set (Real × Hemisphere.Plane v) := C ⁻¹' range graph
  let N : Set (Real × Hemisphere.Plane v) := {z | z ∈ S ∧ 0 ≤ z.1}
  have hheight (z : Real × Hemisphere.Plane v) : inner Real v (C z) = z.1 :=
    inner_heightCoordinates hv z
  have hproject (z : Real × Hemisphere.Plane v) :
      (Hemisphere.Plane v).orthogonalProjectionOnto (C z) = z.2 :=
    congrArg Prod.snd (C.symm_apply_apply z)
  have hbelt (t : Real) (q : Hemisphere.Plane v) (ht : |t| ≤ 1 / 4) :
      (t, q) ∈ S ↔ q ∈ sphere (0 : Hemisphere.Plane v) 1 := by
    change C (t, q) ∈ range graph ↔ _
    rw [mem_sphere_zero_iff_norm]
    have h := mem_boundedCylinder_sphere_iff_of_height_belt v hv (C (t, q))
      (by rwa [hheight])
    simpa only [hproject] using h
  have hsym (t : Real) (q : Hemisphere.Plane v) :
      (t, q) ∈ S ↔ (-t, q) ∈ S := by
    have heq : (Hemisphere.Plane v).reflection (C (t, q)) = C (-t, q) := by
      change (Hemisphere.Plane v).reflection (t • v + (q : E3)) = (-t) • v + (q : E3)
      rw [map_add, map_smul, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
        Submodule.reflection_mem_subspace_eq_self q.property]
      simp
    change C (t, q) ∈ range graph ↔ C (-t, q) ∈ range graph
    rw [← heq]
    exact (reflection_mem_boundedCylinder_sphere_iff v (C (t, q))).symm
  have hnorth : C '' N = graph '' {p : S2 | 0 ≤ inner Real v (p : E3)} := by
    apply Subset.antisymm
    · rintro y ⟨z, ⟨hz, hz0⟩, rfl⟩
      obtain ⟨p, hp⟩ := hz
      refine ⟨p, ?_, hp⟩
      have hh : boundedCylinderRadius v p * inner Real v (p : E3) = z.1 := by
        rw [← inner_smul_right]
        exact (congrArg (inner Real v) hp).trans (hheight z)
      change 0 ≤ inner Real v (p : E3)
      nlinarith [boundedCylinderRadius_pos v p]
    · rintro y ⟨p, hp, rfl⟩
      refine ⟨C.symm (graph p), ⟨?_, ?_⟩, C.apply_symm_apply _⟩
      · change C (C.symm (graph p)) ∈ range graph
        rw [C.apply_symm_apply]
        exact mem_range_self p
      · change 0 ≤ inner Real v (boundedCylinderRadius v p • (p : E3))
        rw [inner_smul_right]
        exact mul_nonneg (boundedCylinderRadius_pos v p).le hp
  obtain ⟨B, _, hB, _, _⟩ := exists_boundedCylinder_ambient v hv
  have hpre : C.symm '' (B '' sphere (0 : E3) 1) = S := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      change C (C.symm (B x)) ∈ range graph
      rw [C.apply_symm_apply]
      exact ⟨⟨x, hx⟩, (hB ⟨x, hx⟩).symm⟩
    · rintro ⟨p, hp⟩
      refine ⟨B p, ⟨p, p.property, rfl⟩, ?_⟩
      rw [hB]
      change C.symm (graph p) = z
      rw [hp, C.symm_apply_apply]
  let H := CappedCylinder.unequalHeightDiffeomorph hab hu hw
  let P : (Real × Hemisphere.Plane v) ≃ₘ[Real] (Real × Hemisphere.Plane v) := {
    toEquiv := H.toEquiv.prodCongr A.toEquiv
    contMDiff_toFun := ((H.contDiff.comp contDiff_fst).prodMk
      (A.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := ((H.symm.contDiff.comp contDiff_fst).prodMk
      (A.symm.contDiff.comp contDiff_snd)).contMDiff }
  let F := (B.trans C.symm.toDiffeomorph).trans (P.trans C.toDiffeomorph)
  let K : Real × Hemisphere.Plane v → E3 := fun z => C (z.1, A z.2)
  let V : Real × Hemisphere.Plane v → Real × Hemisphere.Plane v :=
    fun z => (CappedCylinder.unequalHeight a b u w z.1, z.2)
  have himage : F '' sphere (0 : E3) 1 = K '' (V '' S) := by
    calc
      F '' sphere (0 : E3) 1 = (C ∘ P) '' (C.symm '' (B '' sphere (0 : E3) 1)) := by
        rw [← image_comp, ← image_comp]
        rfl
      _ = (C ∘ P) '' S := by rw [hpre]
      _ = K '' (V '' S) := by rw [← image_comp]; rfl
  have hlower : K '' ((fun z : Real × Hemisphere.Plane v => (a - u * z.1, z.2)) '' N) =
      liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A '' (C '' N) := by
    rw [← image_comp, ← image_comp]
    apply image_congr
    intro z _
    change (a - u * z.1) • v + (A z.2 : E3) =
      liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A (C z)
    rw [liftPlaneDiffeomorph_apply, hheight, hproject]
    simp [sub_eq_add_neg]
  have hupper : K '' ((fun z : Real × Hemisphere.Plane v => (b + w * z.1, z.2)) '' N) =
      liftPlaneDiffeomorph hv b w hw.ne' A '' (C '' N) := by
    rw [← image_comp, ← image_comp]
    apply image_congr
    intro z _
    change (b + w * z.1) • v + (A z.2 : E3) =
      liftPlaneDiffeomorph hv b w hw.ne' A (C z)
    rw [liftPlaneDiffeomorph_apply, hheight, hproject]
  refine ⟨F, ?_⟩
  rw [himage, show V '' S = _ from
    CappedCylinder.image_heightMap_eq_caps_union_cylinder S
      (sphere (0 : Hemisphere.Plane v) 1) hbelt hsym hab hu hw _
      (CappedCylinder.contDiff_unequalHeight a b u w).continuous
      (CappedCylinder.strictMono_unequalHeight hab hu hw).monotone
      (CappedCylinder.unequalHeight_of_le a b u w)
      (CappedCylinder.unequalHeight_of_ge a b u w),
    image_union, image_union, hlower, hupper, hnorth]
  rfl

theorem exists_ambient_capped_cylinder
    {v : E3} (hv : ‖v‖ = 1) (a b : Real) (hab : a ≤ b)
    (s : Real) (hs : 0 < s)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv a (-s) (neg_ne_zero.mpr hs.ne') A ''
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | 0 ≤ inner Real v (p : E3)})) ∪
        ((fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
          (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1)) ∪
        (liftPlaneDiffeomorph hv b s hs.ne' A ''
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | 0 ≤ inner Real v (p : E3)})) :=
  exists_ambient_capped_cylinder_of_scales hv a b hab s s hs hs A

end Poincare.Manifold.Schoenflies
