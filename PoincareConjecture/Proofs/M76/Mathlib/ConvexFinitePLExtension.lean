import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.ConicalAffineExtension










set_option autoImplicit false

open Set Geometry

namespace Homeomorph




theorem IsFinitePL.exists_convex_extension_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s : Set E} {t : Set F} {e : frontier s ≃ₜ frontier t} (he : e.IsFinitePL)
    (hs : IsCompact s) (ht : IsCompact t) (hscv : Convex ℝ s) (htcv : Convex ℝ t)
    (hs0 : (0 : E) ∈ interior s) (ht0 : (0 : F) ∈ interior t) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧ ∀ x : frontier s,
      H ⟨x, hs.isClosed.frontier_subset x.property⟩ =
        ⟨e x, ht.isClosed.frontier_subset (e x).property⟩ := by
  classical
  obtain ⟨f, ⟨K, hK, hspaceK, hf⟩, hef⟩ := he
  have hinj : InjOn f K.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hspaceK ▸ hx⟩ = e ⟨y, hspaceK ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let L := hf.embeddedImage hinj
  have hspaceL : L.space = frontier t := by
    rw [hf.embeddedImage_space, hspaceK]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinK := K.linearIndependent_faces_of_space_subset_frontier hscv hs0 hspaceK.subset
  have hradK : InjOn (NormedSpace.normalize : E → E) K.space := by
    rw [hspaceK]
    exact hscv.injOn_normalize_frontier hs0
  have hlinL := L.linearIndependent_faces_of_space_subset_frontier htcv ht0 hspaceL.subset
  have hradL : InjOn (NormedSpace.normalize : F → F) L.space := by
    rw [hspaceL]
    exact htcv.injOn_normalize_frontier ht0
  have hconeK := K.coneAtZero_space_of_frontier hlinK hradK hs hscv hs0 hspaceK
  have hconeL := L.coneAtZero_space_of_frontier hlinL hradL ht htcv ht0 hspaceL
  obtain ⟨H, ⟨p, hp, hHp⟩, hbase⟩ := hf.exists_cone_extension hinj hK hlinK hradK hlinL hradL
  let G := (Homeomorph.setCongr hconeK.symm).trans (H.trans (Homeomorph.setCongr hconeL))
  have hG (x : s) : (G x : F) =
      (H ⟨x, hconeK.symm ▸ x.property⟩ : F) := rfl
  refine ⟨G, ⟨p, ?_, fun x => (hG x).trans (hHp _)⟩, ?_⟩
  · rwa [hconeK] at hp
  · intro x
    apply Subtype.ext
    rw [hG]
    exact (hbase ⟨x, hspaceK.symm ▸ x.property⟩).trans (hef x).symm

end Homeomorph
