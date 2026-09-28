import PoincareConjecture.Proofs.M76.Mathlib.TruncatedStarBoundaryTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.ConicalHeightExtension
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [DecidableEq E]

theorem IsFinitePL.exists_truncatedStar_height_extension
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hα : α < 0) (hβ : 0 < β)
    (hne : (K.link 0).space.Nonempty)
    {s : Set F} {e : K.truncatedStarBoundary L α β ≃ₜ frontier s}
    (he : e.IsFinitePL) (hs : IsCompact s) (hscv : Convex ℝ s)
    (hs0 : (0 : F) ∈ interior s) (A : F →ₗ[ℝ] ℝ)
    (hheight : ∀ x, A (e x) = L x) :
    ∃ G : ((K.closedStar 0).space ∩ {x | L x ∈ Icc α β} : Set E) ≃ₜ s,
      G.IsFinitePL ∧ (∀ x, A (G x) = L x) ∧
        ∀ x : K.truncatedStarBoundary L α β,
          (G ⟨x, K.truncatedStarBoundary_subset_band L (hα.trans hβ).le x.property⟩ : F) =
            e x := by
  classical
  obtain ⟨f, ⟨J, hJ, hJs, hf⟩, hef⟩ := he
  obtain ⟨D, hD, hDs, hlinD⟩ := K.exists_finite_truncatedStarBoundary_complex hK L hα hβ
  obtain ⟨R, hR, hRJ, hRD⟩ := J.exists_finite_refinement_of_space_subset D hJ hD
    (fun _ hx => hDs.symm.subset (hJs.subset hx))
  have hRs : R.space = K.truncatedStarBoundary L α β := hRJ.space_eq.trans hJs
  have hfR := hRJ.affineOnFaces hf
  have hinj : InjOn f R.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hRs ▸ hx⟩ = e ⟨y, hRs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let T := hfR.embeddedImage hinj
  have hTs : T.space = frontier s := by
    rw [hfR.embeddedImage_space, hRs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinR := R.linearIndependent_faces_of_face_containment D hlinD hRD
  have hradR : InjOn (NormedSpace.normalize : E → E) R.space := by
    rw [hRs]
    exact K.injOn_normalize_truncatedStarBoundary L hα hβ
  have hlinT := T.linearIndependent_faces_of_space_subset_frontier hscv hs0 hTs.subset
  have hradT : InjOn (NormedSpace.normalize : F → F) T.space := by
    rw [hTs]
    exact hscv.injOn_normalize_frontier hs0
  have hRne : R.space.Nonempty := hRs.symm ▸
    K.truncatedStarBoundary_nonempty L hα hβ hne
  have hconeR : (R.coneAtZero hlinR hradR).space =
      (K.closedStar 0).space ∩ {x | L x ∈ Icc α β} := by
    rw [R.coneAtZero_space_eq_convexJoin hlinR hradR hRne, hRs]
    exact K.convexJoin_truncatedStarBoundary_eq_band L hα hβ hne
  have hconeT := T.coneAtZero_space_of_frontier hlinT hradT hs hscv hs0 hTs
  have hfheight (x : E) (hx : x ∈ R.space) : A (f x) = L x := by
    rw [← hef ⟨x, hRs.subset hx⟩]
    exact hheight ⟨x, hRs.subset hx⟩
  obtain ⟨H, hH, hHheight, hbase⟩ := hfR.exists_height_preserving_cone_extension
    hinj hR hlinR hradR hlinT hradT L A hfheight
  let G := (Homeomorph.setCongr hconeR.symm).trans
    (H.trans (Homeomorph.setCongr hconeT))
  refine ⟨G, hH.setCongr hconeR hconeT, ?_, ?_⟩
  · intro x
    exact hHheight ⟨x, hconeR.symm ▸ x.property⟩
  · intro x
    change (H ⟨x, _⟩ : F) = e x
    exact (hbase ⟨x, hRs.symm ▸ x.property⟩).trans (hef x).symm

end Homeomorph
