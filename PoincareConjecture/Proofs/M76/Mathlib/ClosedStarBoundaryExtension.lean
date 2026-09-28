import PoincareConjecture.Proofs.M76.Mathlib.LinearIndependentFaceRefinement
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.RadialConeBoundary










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [DecidableEq E]





theorem IsFinitePL.exists_closedStar_extension_radial
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (hne : (K.link 0).space.Nonempty)
    {T : Set F} {e : (K.link 0).space ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hcv : Convex ℝ T) (hT0 : (0 : F) ∈ interior T) :
    ∃ (g : E → F) (H : (K.closedStar 0).space ≃ₜ T), H.IsFinitePL ∧
      (∀ x, (H x : F) = g x) ∧ g 0 = 0 ∧
      (∀ x : (K.link 0).space, g x = e x) ∧
      ∀ (x : (K.link 0).space) (r : ℝ), r ∈ Icc 0 1 →
        g (r • (x : E)) = r • (e x : F) := by
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
  have hLs : L.space = frontier T := by
    rw [hfR.embeddedImage_space, hRs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinR := R.linearIndependent_faces_of_face_containment (K.link 0)
    (fun _ hs => SimplicialComplex.linearIndependent_of_mem_link_zero hs) hRK
  have hradR : InjOn (NormedSpace.normalize : E → E) R.space :=
    hRs.symm ▸ K.injOn_normalize_link
  have hlinL := L.linearIndependent_faces_of_space_subset_frontier hcv hT0 hLs.subset
  have hradL : InjOn (NormedSpace.normalize : F → F) L.space :=
    hLs.symm ▸ hcv.injOn_normalize_frontier hT0
  have hconeR : (R.coneAtZero hlinR hradR).space = (K.closedStar 0).space := by
    rw [R.coneAtZero_space_eq_convexJoin hlinR hradR (hRs.symm ▸ hne), hRs,
      ← SimplicialComplex.coneAtZero_link_eq_closedStar K hzero]
    exact ((K.link 0).coneAtZero_space_eq_convexJoin
      (fun _ hs => SimplicialComplex.linearIndependent_of_mem_link_zero hs)
      K.injOn_normalize_link hne).symm
  have hconeL := L.coneAtZero_space_of_frontier hlinL hradL hT hcv hT0 hLs
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




theorem IsFinitePL.exists_closedStar_extension
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (hne : (K.link 0).space.Nonempty)
    {T : Set F} {e : (K.link 0).space ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hcv : Convex ℝ T) (hT0 : (0 : F) ∈ interior T) :
    ∃ H : (K.closedStar 0).space ≃ₜ T, H.IsFinitePL ∧
      ∀ x : (K.link 0).space,
        H ⟨x, SimplicialComplex.space_subset_of_le (K.link_le_closedStar 0) x.property⟩ =
          ⟨e x, hT.isClosed.frontier_subset (e x).property⟩ := by
  obtain ⟨g, H, hH, hHg, _, hbase, _⟩ :=
    he.exists_closedStar_extension_radial K hK hzero hne hT hcv hT0
  refine ⟨H, hH, fun x => ?_⟩
  apply Subtype.ext
  exact (hHg ⟨x,
    SimplicialComplex.space_subset_of_le (K.link_le_closedStar 0) x.property⟩).trans (hbase x)




theorem IsFinitePL.isFinitePLBallPair_closedStar
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (hne : (K.link 0).space.Nonempty)
    {T : Set F} {e : (K.link 0).space ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hcv : Convex ℝ T) (hT0 : (0 : F) ∈ interior T) :
    IsFinitePLBallPair F (K.closedStar 0).space (K.link 0).space := by
  obtain ⟨H, hH, hkeep⟩ := he.exists_closedStar_extension K hK hzero hne hT hcv hT0
  have hsub := SimplicialComplex.space_subset_of_le (K.link_le_closedStar 0)
  exact ⟨hsub, T, hT, hcv, ⟨0, hT0⟩, H, hH,
    H.mem_subset_iff_of_extension e hsub hT.isClosed.frontier_subset hkeep⟩

end Homeomorph
