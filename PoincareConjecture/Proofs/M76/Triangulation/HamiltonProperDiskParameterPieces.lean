import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FullSimplexBasis










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}





theorem HamiltonProperDiskTriangulation.exists_original_triangle_parameter
    (T : HamiltonProperDiskTriangulation R D b)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 3) :
    ∃ P : V2 →ᴬ[ℝ] E, Function.Injective P ∧
      (∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x) ∧
      P '' convexHull ℝ (T.inverse '' (s : Set E)) = convexHull ℝ (s : Set E) ∧
      ∀ x ∈ convexHull ℝ (T.inverse '' (s : Set E)), T.inverse (P x) = x := by
  classical
  have hD (x : E) (hx : x ∈ T.disk.space) : x ∈ D := T.disk_space.subset hx
  have hinj : InjOn T.inverse T.disk.space := by
    intro x hx y hy hxy
    have h : b.symm ⟨x, hD x hx⟩ = b.symm ⟨y, hD y hy⟩ := by
      apply Subtype.ext
      exact (T.inverse_eq ⟨x, hD x hx⟩).symm.trans
        (hxy.trans (T.inverse_eq ⟨y, hD y hy⟩))
    exact congrArg Subtype.val (b.symm.injective h)
  let f : V2 → E := fun x => if hx : x ∈ Cube then (b ⟨x, hx⟩ : E) else 0
  have hleft : LeftInvOn f T.inverse T.disk.space := by
    intro x hx
    rw [T.inverse_eq ⟨x, hD x hx⟩]
    simp only [f, dif_pos (b.symm ⟨x, hD x hx⟩).property, b.apply_symm_apply]
  have hright (x : V2) (hx : x ∈ Cube) : T.inverse (f x) = x := by
    rw [show f x = (b ⟨x, hx⟩ : E) from dif_pos hx, T.inverse_eq]
    exact congrArg Subtype.val (b.symm_apply_apply ⟨x, hx⟩)
  let L := T.inverse_affine.embeddedImage hinj
  have hLspace : L.space = Cube := by
    rw [T.inverse_affine.embeddedImage_space]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [T.inverse_eq ⟨x, hD x hx⟩]
      exact (b.symm ⟨x, hD x hx⟩).property
    · intro x hx
      refine ⟨b ⟨x, hx⟩, T.disk_space.symm.subset (b ⟨x, hx⟩).property, ?_⟩
      exact (T.inverse_eq (b ⟨x, hx⟩)).trans
        (congrArg Subtype.val (b.symm_apply_apply ⟨x, hx⟩))
  have hf : L.AffineOnFaces f := T.inverse_affine.inverse_on_embeddedImage hinj hleft
  let t : Finset V2 := s.image T.inverse
  have ht : t ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have htcard : t.card = Module.finrank ℝ V2 + 1 := by
    have hsi : InjOn T.inverse (s : Set E) := hinj.mono (T.disk.subset_space hs)
    have hct : t.card = s.card := Finset.card_image_iff.mpr hsi
    simpa [hcard] using hct
  have htset : (t : Set V2) = T.inverse '' (s : Set E) := Finset.coe_image
  obtain ⟨P, hP⟩ := hf t ht
  have hPs (x : E) (hx : x ∈ convexHull ℝ (s : Set E)) : P (T.inverse x) = x := by
    have hxi : T.inverse x ∈ convexHull ℝ (t : Set V2) := by
      rw [htset, ← T.inverse_affine.image_convexHull hs]
      exact mem_image_of_mem T.inverse hx
    exact (hP hxi).symm.trans (hleft (T.disk.convexHull_subset_space hs hx))
  have hPr (x : V2) (hx : x ∈ convexHull ℝ (t : Set V2)) : T.inverse (P x) = x := by
    rw [← hP hx]
    exact hright x (hLspace.subset (L.convexHull_subset_space ht hx))
  have hPi : InjOn P.toAffineMap (convexHull ℝ (t : Set V2)) := by
    intro x hx y hy hxy
    exact (hPr x hx).symm.trans ((congrArg T.inverse hxy).trans (hPr y hy))
  have hspan : affineSpan ℝ (convexHull ℝ (t : Set V2)) = ⊤ := by
    rw [affineSpan_convexHull]
    simpa using ((L.indep ht).affineBasisOfCard htcard).tot
  have hPinj : Function.Injective P := by
    have hi := P.toAffineMap.injOn_affineSpan_of_injOn_convex
      (convex_convexHull ℝ _)
      (Finset.coe_nonempty.mpr (L.nonempty_of_mem_faces ht)).convexHull hPi
    rw [hspan] at hi
    intro x y hxy
    exact hi (by trivial) (by trivial) hxy
  refine ⟨P, hPinj, hPs, ?_, ?_⟩
  · rw [← T.inverse_affine.image_convexHull hs]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hPs x hx]
      exact hx
    · intro hy
      exact ⟨T.inverse y, mem_image_of_mem T.inverse hy, hPs y hy⟩
  · intro x hx
    exact hPr x (htset.symm ▸ hx)

end PoincareConjecture.M76.HamiltonIndexOne
