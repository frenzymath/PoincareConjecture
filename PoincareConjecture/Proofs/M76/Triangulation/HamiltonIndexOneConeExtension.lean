import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.RadialConeBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_radial_convex_extension
    {C : Set E} {D : Set F} {e : frontier C ≃ₜ frontier D}
    (he : e.IsFinitePL) (hC : IsCompact C) (hD : IsCompact D)
    (hcvC : Convex ℝ C) (hcvD : Convex ℝ D)
    (hC0 : (0 : E) ∈ interior C) (hD0 : (0 : F) ∈ interior D) :
    ∃ (g : E → F) (H : C ≃ₜ D), H.IsFinitePL ∧
      (∀ x : C, (H x : F) = g x) ∧ g 0 = 0 ∧
      ∀ (x : E) (hx : x ∈ frontier C) (t : ℝ), t ∈ Icc 0 1 →
        g (t • x) = t • (e ⟨x, hx⟩ : F) := by
  classical
  obtain ⟨f, ⟨K, hK, hKs, hf⟩, hef⟩ := he
  have hinj : InjOn f K.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hKs ▸ hx⟩ = e ⟨y, hKs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let L := hf.embeddedImage hinj
  have hLs : L.space = frontier D := by
    rw [hf.embeddedImage_space, hKs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinK := K.linearIndependent_faces_of_space_subset_frontier hcvC hC0 hKs.subset
  have hradK : InjOn (NormedSpace.normalize : E → E) K.space := by
    rw [hKs]
    exact hcvC.injOn_normalize_frontier hC0
  have hlinL := L.linearIndependent_faces_of_space_subset_frontier hcvD hD0 hLs.subset
  have hradL : InjOn (NormedSpace.normalize : F → F) L.space := by
    rw [hLs]
    exact hcvD.injOn_normalize_frontier hD0
  have hconeK := K.coneAtZero_space_of_frontier hlinK hradK hC hcvC hC0 hKs
  have hconeL := L.coneAtZero_space_of_frontier hlinL hradL hD hcvD hD0 hLs
  obtain ⟨g, H, hg, hg0, hbase, hH⟩ :=
    hf.exists_cone_extension_affine hinj hK hlinK hradK hlinL hradL
  let G := (Homeomorph.setCongr hconeK.symm).trans
    (H.trans (Homeomorph.setCongr hconeL))
  have hG (x : C) : (G x : F) = g x := hH ⟨x, hconeK.symm ▸ x.property⟩
  have hGPL : G.IsFinitePL := by
    refine ⟨g, ?_, hG⟩
    have h := hg.finitePiecewiseAffineOn
      (SimplicialComplex.finite_coneAtZero_faces hK hlinK hradK)
    rwa [hconeK] at h
  refine ⟨g, G, hGPL, hG, hg0, ?_⟩
  intro x hx t ht
  rw [hg.cone_extension_smul hg0 hbase (hKs.symm ▸ hx) ht, ← hef ⟨x, hx⟩]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem radial_extension_image_convexJoin
    {C : Set E} {D : Set F} (e : frontier C ≃ₜ frontier D)
    (g : E → F)
    (hrad : ∀ (x : E) (hx : x ∈ frontier C) (t : ℝ), t ∈ Icc 0 1 →
      g (t • x) = t • (e ⟨x, hx⟩ : F))
    {q : Set E} (hq : q ⊆ frontier C) :
    g '' convexJoin ℝ {0} q =
      convexJoin ℝ {0} ((fun x : frontier C => (e x : F)) ''
        ((Subtype.val : frontier C → E) ⁻¹' q)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, t, ht, rfl⟩ := (mem_convexJoin_zero_iff q x).mp hx
    rw [hrad z (hq hz) t ht]
    exact (mem_convexJoin_zero_iff _ _).mpr
      ⟨e ⟨z, hq hz⟩, ⟨⟨z, hq hz⟩, hz, rfl⟩, t, ht, rfl⟩
  · intro hy
    obtain ⟨z, ⟨w, hw, rfl⟩, t, ht, rfl⟩ :=
      (mem_convexJoin_zero_iff _ y).mp hy
    refine ⟨t • (w : E), (mem_convexJoin_zero_iff q _).mpr
      ⟨w, hw, t, ht, rfl⟩, ?_⟩
    exact hrad w w.property t ht

end PoincareConjecture.M76.HamiltonIndexOne
