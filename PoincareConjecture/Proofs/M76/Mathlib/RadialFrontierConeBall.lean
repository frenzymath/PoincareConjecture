import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsFinitePL.exists_radial_boundary_cone_extension
    {S C : Set E} {T : Set F} {e : S ≃ₜ frontier T} (he : e.IsFinitePL)
    (hcv : Convex ℝ C) (hC0 : (0 : E) ∈ interior C)
    (hSC : S ⊆ frontier C) (hne : S.Nonempty)
    (hT : IsCompact T) (hTcv : Convex ℝ T) (hT0 : (0 : F) ∈ interior T) :
    ∃ H : (convexJoin ℝ {0} S) ≃ₜ T, H.IsFinitePL ∧
      ∀ x : S, H ⟨x, subset_convexJoin_right (singleton_nonempty 0) x.property⟩ =
        ⟨e x, hT.isClosed.frontier_subset (e x).property⟩ := by
  classical
  obtain ⟨f, ⟨K, hK, hKs, hf⟩, hef⟩ := he
  have hinj : InjOn f K.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hKs ▸ hx⟩ = e ⟨y, hKs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let L := hf.embeddedImage hinj
  have hLs : L.space = frontier T := by
    rw [hf.embeddedImage_space, hKs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinK := K.linearIndependent_faces_of_space_subset_frontier hcv hC0
    (hKs.subset.trans hSC)
  have hradK : InjOn (NormedSpace.normalize : E → E) K.space :=
    (hcv.injOn_normalize_frontier hC0).mono (hKs.subset.trans hSC)
  have hlinL := L.linearIndependent_faces_of_space_subset_frontier hTcv hT0 hLs.subset
  have hradL : InjOn (NormedSpace.normalize : F → F) L.space :=
    (hTcv.injOn_normalize_frontier hT0).mono hLs.subset
  have hconeK : (K.coneAtZero hlinK hradK).space = convexJoin ℝ {0} S := by
    rw [K.coneAtZero_space_eq_convexJoin hlinK hradK (hKs.symm ▸ hne), hKs]
  have hconeL := L.coneAtZero_space_of_frontier hlinL hradL hT hTcv hT0 hLs
  obtain ⟨H, hH, hbase⟩ := hf.exists_cone_extension hinj hK hlinK hradK hlinL hradL
  let G := (Homeomorph.setCongr hconeK.symm).trans
    (H.trans (Homeomorph.setCongr hconeL))
  refine ⟨G, hH.setCongr hconeK hconeL, fun x => ?_⟩
  apply Subtype.ext
  change (H ⟨x, _⟩ : F) = e x
  exact (hbase ⟨x, hKs.symm ▸ x.property⟩).trans (hef x).symm

theorem IsFinitePL.isFinitePLBallPair_radial_cone
    {S C : Set E} {T : Set F} {e : S ≃ₜ frontier T} (he : e.IsFinitePL)
    (hcv : Convex ℝ C) (hC0 : (0 : E) ∈ interior C)
    (hSC : S ⊆ frontier C) (hne : S.Nonempty)
    (hT : IsCompact T) (hTcv : Convex ℝ T) (hTne : (interior T).Nonempty) :
    IsFinitePLBallPair F (convexJoin ℝ {0} S) S := by
  obtain ⟨p, hp⟩ := hTne
  let a : F ≃ᴬ[ℝ] F := ContinuousAffineEquiv.constVAdd ℝ F (-p)
  have ha0 : a p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hTa : IsCompact (a '' T) := hT.image a.continuous
  have hcvTa : Convex ℝ (a '' T) := hTcv.affine_image a.toAffineEquiv.toAffineMap
  have h0Ta : (0 : F) ∈ interior (a '' T) := by
    change (0 : F) ∈ interior (a.toHomeomorph '' T)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨p, hp, ha0⟩
  have hfront : a '' frontier T = frontier (a '' T) := a.toHomeomorph.image_frontier T
  let d := e.trans (a.toHomeomorph.image (frontier T))
  have hd : d.IsFinitePL := by
    obtain ⟨f, hf, hef⟩ := he
    refine ⟨a ∘ f, hf.postcomp a.toContinuousAffineMap, fun x => ?_⟩
    change a (e x) = a (f x)
    rw [hef]
  let d' := d.trans (Homeomorph.setCongr hfront)
  have hd' : d'.IsFinitePL := hd.setCongr rfl hfront
  obtain ⟨H, hH, hbase⟩ := hd'.exists_radial_boundary_cone_extension
    hcv hC0 hSC hne hTa hcvTa h0Ta
  have hScone : S ⊆ convexJoin ℝ {0} S :=
    subset_convexJoin_right (singleton_nonempty 0)
  exact ⟨hScone, a '' T, hTa, hcvTa, ⟨0, h0Ta⟩, H, hH,
    H.mem_subset_iff_of_extension d' hScone hTa.isClosed.frontier_subset hbase⟩

end Homeomorph
