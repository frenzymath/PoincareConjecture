import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarBoundaryExtension
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexCone

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem IsFinitePL.exists_closedStar_section_extension_radial
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (hne : (K.link 0).space.Nonempty)
    {C : Set E}
    {e : (K.link 0).space ≃ₜ ((K.closedStar 0).space ∩ frontier C : Set E)}
    (he : e.IsFinitePL) (hC : IsCompact C) (hcv : Convex ℝ C)
    (hC0 : (0 : E) ∈ interior C) (hdisj : Disjoint C (K.link 0).space) :
    ∃ (g : E → E)
      (H : (K.closedStar 0).space ≃ₜ ((K.closedStar 0).space ∩ C : Set E)),
      H.IsFinitePL ∧ (∀ x, (H x : E) = g x) ∧ g 0 = 0 ∧
      (∀ x : (K.link 0).space, g x = e x) ∧
      ∀ (x : (K.link 0).space) (r : ℝ), r ∈ Icc 0 1 →
        g (r • (x : E)) = r • (e x : E) := by
  classical
  obtain ⟨f, ⟨J, hJ, hJs, hf⟩, hef⟩ := he
  obtain ⟨R, hR, hRJ, hRK⟩ := J.exists_finite_refinement_of_space_subset
    (K.link 0) hJ (SimplicialComplex.finite_link_faces hK 0) hJs.subset
  have hRs : R.space = (K.link 0).space := hRJ.space_eq.trans hJs
  have hfR := hRJ.affineOnFaces hf
  have hinj : InjOn f R.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hRs ▸ hx⟩ = e ⟨y, hRs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let L := hfR.embeddedImage hinj
  have hLs : L.space = (K.closedStar 0).space ∩ frontier C := by
    rw [hfR.embeddedImage_space, hRs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hLfrontier : L.space ⊆ frontier C := hLs.subset.trans inter_subset_right
  have hsection : ((K.closedStar 0).space ∩ frontier C).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e ⟨x, hx⟩, (e ⟨x, hx⟩).property⟩
  have hlinR := R.linearIndependent_faces_of_face_containment (K.link 0)
    (fun _ hs => SimplicialComplex.linearIndependent_of_mem_link_zero hs) hRK
  have hradR : InjOn (NormedSpace.normalize : E → E) R.space :=
    hRs.symm ▸ K.injOn_normalize_link
  have hlinL := L.linearIndependent_faces_of_space_subset_frontier hcv hC0 hLfrontier
  have hradL : InjOn (NormedSpace.normalize : E → E) L.space :=
    (hcv.injOn_normalize_frontier hC0).mono hLfrontier
  have hconeR : (R.coneAtZero hlinR hradR).space = (K.closedStar 0).space := by
    rw [R.coneAtZero_space_eq_convexJoin hlinR hradR (hRs.symm ▸ hne), hRs,
      ← SimplicialComplex.coneAtZero_link_eq_closedStar K hzero]
    exact ((K.link 0).coneAtZero_space_eq_convexJoin
      (fun _ hs => SimplicialComplex.linearIndependent_of_mem_link_zero hs)
      K.injOn_normalize_link hne).symm
  have hconeL : (L.coneAtZero hlinL hradL).space = (K.closedStar 0).space ∩ C := by
    rw [L.coneAtZero_space_eq_convexJoin hlinL hradL (hLs.symm ▸ hsection), hLs]
    exact K.convexJoin_closedStar_frontier_eq_inter hC hcv hC0 hdisj hsection
  obtain ⟨g, H, hg, hg0, hbase, hH⟩ :=
    hfR.exists_cone_extension_affine hinj hR hlinR hradR hlinL hradL
  have hHPL : H.IsFinitePL :=
    ⟨g, hg.finitePiecewiseAffineOn
      (SimplicialComplex.finite_coneAtZero_faces hR hlinR hradR), hH⟩
  let G := (Homeomorph.setCongr hconeR.symm).trans
    (H.trans (Homeomorph.setCongr hconeL))
  refine ⟨g, G, hHPL.setCongr hconeR hconeL, ?_, hg0, ?_, ?_⟩
  · intro x
    exact hH ⟨x, hconeR.symm.subset x.property⟩
  · intro x
    exact (hbase (hRs.symm.subset x.property)).trans (hef x).symm
  · intro x r hr
    rw [hg.cone_extension_smul hg0 hbase (hRs.symm.subset x.property) hr, ← hef x]

end Homeomorph
