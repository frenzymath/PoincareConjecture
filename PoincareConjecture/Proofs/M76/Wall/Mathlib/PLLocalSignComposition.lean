import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLLocalDeterminantSign
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ComposableAffinePatches

set_option autoImplicit false

open Set Metric

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem plLocalSign_trans (h k : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) (hk : k ∈ piecewiseAffineGroupoid E)
    (x : (h.trans k).source) :
    plLocalSign (h.trans k) ((piecewiseAffineGroupoid E).trans hh hk) x =
      plLocalSign k hk ⟨h x, x.property.2⟩ *
        plLocalSign h hh ⟨x, x.property.1⟩ := by
  let hhk := (piecewiseAffineGroupoid E).trans hh hk
  obtain ⟨K, hK, hxK, hKs, hf, _, _⟩ :=
    exists_finite_paired_facet_orientation h hh x.property.1
  obtain ⟨L, hL, hxL, hLs, hg, _, _⟩ :=
    exists_finite_paired_facet_orientation k hk x.property.2
  obtain ⟨M, hM, hxM, hMs, hcomp, _, _⟩ :=
    exists_finite_paired_facet_orientation (h.trans k) hhk x.property
  obtain ⟨r, hr, hballL⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxL)
  have hopen : IsOpen (interior K.space ∩
      (interior M.space ∩ (h.source ∩ h ⁻¹' ball (h x) r))) :=
    isOpen_interior.inter (isOpen_interior.inter (h.isOpen_inter_preimage isOpen_ball))
  have hxopen : (x : E) ∈ interior K.space ∩
      (interior M.space ∩ (h.source ∩ h ⁻¹' ball (h x) r)) :=
    ⟨hxK, hxM, x.property.1, mem_ball_self hr⟩
  obtain ⟨q, hq, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hxopen)
  have hUK : ball (x : E) q ⊆ K.space := fun _ hy => interior_subset (hball hy).1
  have hUM : ball (x : E) q ⊆ M.space := fun _ hy => interior_subset (hball hy).2.1
  have hUs : ball (x : E) q ⊆ h.source := fun _ hy => (hball hy).2.2.1
  have hUV : MapsTo h (ball (x : E) q) (ball (h x) r) := fun _ hy => (hball hy).2.2.2
  obtain ⟨t, u, v, A, B, C, _, hA, hB, hC, _, _, _, _, _, _, _, hCAB⟩ :=
    exists_composable_affine_patches h k K L M hK hL hM hf hg hcomp
      isOpen_ball ⟨x, mem_ball_self hq⟩ hUK hUM hUs hUV hballL
      (fun _ hy => hLs (hballL hy))
  rw [plLocalSign_eq_of_active_face (h.trans k) hhk M hM hMs hcomp isOpen_ball
    (convex_ball (x : E) q) hUM x (mem_ball_self hq) v C hC]
  rw [plLocalSign_eq_of_active_face k hk L hL hLs hg isOpen_ball
    (convex_ball (h x) r) hballL ⟨h x, x.property.2⟩ (mem_ball_self hr) u B hB]
  rw [plLocalSign_eq_of_active_face h hh K hK hKs hf isOpen_ball
    (convex_ball (x : E) q) hUK ⟨x, x.property.1⟩ (mem_ball_self hq) t A hA]
  rw [hCAB]
  change SignType.sign (LinearMap.det (B.toAffineMap.linear.comp A.toAffineMap.linear)) = _
  rw [LinearMap.det_comp, sign_mul]

private theorem sign_eq_of_product_one {a b : SignType} (h : a * b = 1) : a = b := by
  cases a <;> cases b <;> simp_all

theorem plLocalSign_symm (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) (x : h.source) :
    plLocalSign h.symm ((piecewiseAffineGroupoid E).symm hh)
      ⟨h x, h.map_source x.property⟩ = plLocalSign h hh x := by
  let hi := (piecewiseAffineGroupoid E).symm hh
  let hc := (piecewiseAffineGroupoid E).trans hh hi
  let z : (h.trans h.symm).source := ⟨x, x.property, h.map_source x.property⟩
  let y : (OpenPartialHomeomorph.refl E).source := ⟨x, mem_univ _⟩
  have heq : plLocalSign (h.trans h.symm) hc z =
      plLocalSign (OpenPartialHomeomorph.refl E) (piecewiseAffineGroupoid E).id_mem y :=
    plLocalSign_eq_of_eqOn (h.trans h.symm) (OpenPartialHomeomorph.refl E)
      hc (piecewiseAffineGroupoid E).id_mem z.property y.property
      h.open_source x.property (fun w hw => h.left_inv hw)
  have hprod : plLocalSign h.symm hi ⟨h x, h.map_source x.property⟩ *
      plLocalSign h hh x = 1 :=
    (plLocalSign_trans h h.symm hh hi z).symm.trans (heq.trans (plLocalSign_refl y))
  exact sign_eq_of_product_one hprod

theorem plLocalSign_restr (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) {U : Set E} (hU : IsOpen U)
    (x : (h.restr U).source) :
    plLocalSign (h.restr U) (closedUnderRestriction' hh hU) x =
      plLocalSign h hh ⟨x, x.property.1⟩ :=
  plLocalSign_eq_of_eqOn (h.restr U) h (closedUnderRestriction' hh hU) hh
    x.property x.property.1 (h.restr U).open_source x.property (fun _ _ => rfl)

end Geometry
