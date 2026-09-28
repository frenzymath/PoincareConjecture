import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.ImageDisks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.AffineInterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.LocalDiskEdgeCrossing
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageIncidence

set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem AffineOnFaces.exists_planar_image_edge_crossing
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    {f : (ℝ × ℝ) → V3} (hf : K.AffineOnFaces f) (hfi : InjOn f K.space)
    {s : Finset (ℝ × ℝ)} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {x : ℝ × ℝ} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set (ℝ × ℝ))))
    (hxK : x ∈ interior K.space)
    (A : V3 →ᵃ[ℝ] ℝ) (hxzero : A (f x) = 0)
    (hne : ∃ v ∈ s, A (f v) ≠ 0)
    {O : Set V3} (hO : IsOpen O) (hfxO : f x ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      f x ∈ H.source ∧ H.source ⊆ O ∧ H (f x) = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, z ∈ f '' K.space ↔ (H z).1.1 = 0) ∧
      ∀ z ∈ H.source, A z = (H z).2 := by
  classical
  let P := hf.embeddedImage hfi
  have hP : P.faces.Finite := hf.embeddedImage_finite hfi hK
  have hPs : P.space = f '' K.space := hf.embeddedImage_space hfi
  have hbound (t : Finset V3) (ht : t ∈ P.faces) : t.card ≤ 3 := by
    rw [hf.embeddedImage_faces hfi] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    have hc := (K.indep ha).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    have hca : a.card ≤ 3 := by simpa only [Fintype.card_coe, Module.finrank_prod,
      Module.finrank_self, Nat.reduceAdd] using hc
    exact Finset.card_image_le.trans hca
  have hsP : s.image f ∈ P.faces :=
    (hf.image_mem_embeddedImage_iff hfi (K.subset_space hs)).mpr hs
  have hsP2 : (s.image f).card = 2 :=
    (Finset.card_image_iff.mpr (hfi.mono (K.subset_space hs))).trans hs2
  obtain ⟨B, hB⟩ := hf s hs
  have hBi : InjOn B (convexHull ℝ (s : Set (ℝ × ℝ))) := by
    intro a ha b hb hab
    exact hfi (K.convexHull_subset_space hs ha) (K.convexHull_subset_space hs hb)
      ((hB ha).trans (hab.trans (hB hb).symm))
  have hspan := B.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hBi
  have hBx : B x ∈ intrinsicInterior ℝ (B '' convexHull ℝ (s : Set (ℝ × ℝ))) := by
    change B x ∈ intrinsicInterior ℝ (B.toAffineMap '' convexHull ℝ (s : Set (ℝ × ℝ)))
    rw [B.toAffineMap.intrinsicInterior_image_of_injOn _ hspan]
    exact mem_image_of_mem B hx
  have hfx : f x ∈ intrinsicInterior ℝ (convexHull ℝ (s.image f : Set V3)) := by
    rw [Finset.coe_image, ← hf.image_convexHull hs]
    have heq : f '' convexHull ℝ (s : Set (ℝ × ℝ)) =
        B '' convexHull ℝ (s : Set (ℝ × ℝ)) := image_congr hB
    rw [heq, hB (intrinsicInterior_subset hx)]
    exact hBx
  obtain ⟨d, rim, hd, hdP, hxd, hopen⟩ :=
    (hf.finitePiecewiseAffineOn hK).exists_image_interior_disk hfi hxK P hPs
  have hd' := hd.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨H, hxH, hHO, hHzero, hHPL, hHinv, hsurface, hheight⟩ :=
    P.exists_transverse_edge_crossing_chart_of_local_disk hP hbound hsP hsP2 A
      hfx hxzero (by
        obtain ⟨v, hv, hnv⟩ := hne
        exact ⟨f v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hnv⟩)
      hd' hdP hxd hopen hO hfxO
  exact ⟨H, hxH, hHO, hHzero, hHPL, hHinv, by simpa only [hPs] using hsurface, hheight⟩

end Geometry.SimplicialComplex
