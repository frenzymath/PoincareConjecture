import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

theorem IsFinitePL.exists_convex_extension {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s : Set E} {t : Set F} {e : frontier s ≃ₜ frontier t} (he : e.IsFinitePL)
    (hs : IsCompact s) (ht : IsCompact t) (hscv : Convex ℝ s) (htcv : Convex ℝ t)
    (hsne : (interior s).Nonempty) (htne : (interior t).Nonempty) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : frontier s, H ⟨x, hs.isClosed.frontier_subset x.property⟩ =
        ⟨e x, ht.isClosed.frontier_subset (e x).property⟩) ∧
      (∀ x : s, (x : E) ∈ frontier s ↔ (H x : F) ∈ frontier t) := by
  obtain ⟨p, hp⟩ := hsne
  obtain ⟨q, hq⟩ := htne
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  let b : F ≃ᴬ[ℝ] F := ContinuousAffineEquiv.constVAdd ℝ F (-q)
  have ha0 : a p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hb0 : b q = 0 := by change -q + q = 0; exact neg_add_cancel q
  have hsa : IsCompact (a '' s) := hs.image a.continuous
  have htb : IsCompact (b '' t) := ht.image b.continuous
  have hcva : Convex ℝ (a '' s) := hscv.affine_image a.toAffineEquiv.toAffineMap
  have hcvb : Convex ℝ (b '' t) := htcv.affine_image b.toAffineEquiv.toAffineMap
  have hza : (0 : E) ∈ interior (a '' s) := by
    change (0 : E) ∈ interior (a.toHomeomorph '' s)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨p, hp, ha0⟩
  have hzb : (0 : F) ∈ interior (b '' t) := by
    change (0 : F) ∈ interior (b.toHomeomorph '' t)
    rw [← b.toHomeomorph.image_interior]
    exact ⟨q, hq, hb0⟩
  have hfa : a '' frontier s = frontier (a '' s) := a.toHomeomorph.image_frontier s
  have hfb : b '' frontier t = frontier (b '' t) := b.toHomeomorph.image_frontier t
  let d := (a.toHomeomorph.image (frontier s)).symm.trans
    (e.trans (b.toHomeomorph.image (frontier t)))
  let d' := (Homeomorph.setCongr hfa.symm).trans (d.trans (Homeomorph.setCongr hfb))
  have hd : d'.IsFinitePL := (he.affine_conjugate a b).setCongr hfa hfb
  obtain ⟨H, hH, hHe⟩ := hd.exists_convex_extension_zero hsa htb hcva hcvb hza hzb
  let G := (a.toHomeomorph.image s).trans (H.trans (b.toHomeomorph.image t).symm)
  have hG (x : s) : (G x : F) = b.symm (H ⟨a x, mem_image_of_mem a x.property⟩) := rfl
  obtain ⟨f, hf, hHf⟩ := hH
  have hdomain : a.symm '' (a '' s) = s := by simp
  have hPL : G.IsFinitePL := by
    refine ⟨b.symm ∘ (f ∘ a), ?_, ?_⟩
    · have h := (hf.precomp_affineEquiv a).postcomp b.symm.toContinuousAffineMap
      rwa [hdomain] at h
    · intro x
      rw [hG, hHf]
      rfl
  have hboundary (x : frontier s) : G ⟨x, hs.isClosed.frontier_subset x.property⟩ =
      ⟨e x, ht.isClosed.frontier_subset (e x).property⟩ := by
    have hx : a x ∈ frontier (a '' s) := hfa ▸ mem_image_of_mem a x.property
    have h := congrArg (fun y : b '' t => (y : F)) (hHe ⟨a x, hx⟩)
    have hdval : (d' ⟨a x, hx⟩ : F) = b (e x) := by
      change b (e ⟨a.symm (a x), _⟩) = b (e x)
      apply congrArg b
      apply congrArg (fun z : frontier s => (e z : F))
      exact Subtype.ext (a.symm_apply_apply x)
    apply Subtype.ext
    rw [hG, h, hdval, b.symm_apply_apply]
  exact ⟨G, hPL, hboundary, G.mem_subset_iff_of_extension e
    hs.isClosed.frontier_subset ht.isClosed.frontier_subset hboundary⟩

end Homeomorph
