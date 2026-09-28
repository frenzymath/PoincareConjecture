import PoincareConjecture.Proofs.M76.Mathlib.TruncatedStarHeightExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates










set_option autoImplicit false

open Set Geometry

namespace Set




theorem frontier_rectangle_eq_four_sides {a b α β : ℝ}
    (hab : a ≤ b) (hαβ : α ≤ β) :
    frontier (Icc a b ×ˢ Icc α β) =
      ((Icc a b ×ˢ {α}) ∪ (Icc a b ×ˢ {β})) ∪
        (({a} ×ˢ Icc α β) ∪ ({b} ×ˢ Icc α β)) := by
  rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
    frontier_Icc hab, frontier_Icc hαβ]
  ext x
  simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
  tauto

end Set

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem IsFinitePL.exists_truncatedStar_rectangle_filling
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hα : α < 0) (hβ : 0 < β)
    (hne : (K.link 0).space.Nonempty)
    {e : frontier (Icc (0 : ℝ) 1 ×ˢ Icc α β) ≃ₜ K.truncatedStarBoundary L α β}
    (he : e.IsFinitePL) (hheight : ∀ x, L (e x) = (x : ℝ × ℝ).2) :
    ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ
        ((K.closedStar 0).space ∩ {x | L x ∈ Icc α β} : Set E),
      G.IsFinitePL ∧ (∀ x, L (G x) = (x : ℝ × ℝ).2) ∧
        ∀ x : frontier (Icc (0 : ℝ) 1 ×ˢ Icc α β),
          (G ⟨x, (isClosed_Icc.prod isClosed_Icc).frontier_subset x.property⟩ : E) = e x := by
  let P : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc α β
  let a : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-((1 / 2 : ℝ), 0))
  have hasnd (z : ℝ × ℝ) : (a z).2 = z.2 := by
    change -(0 : ℝ) + z.2 = z.2
    simp
  have ha0 : a ((1 / 2 : ℝ), 0) = 0 := by
    change -(((1 / 2 : ℝ), 0) : ℝ × ℝ) + ((1 / 2 : ℝ), 0) = 0
    exact neg_add_cancel _
  have hP : IsCompact P := isCompact_Icc.prod isCompact_Icc
  have hPcv : Convex ℝ P := (convex_Icc _ _).prod (convex_Icc _ _)
  have hPa : IsCompact (a '' P) := hP.image a.continuous
  have hPacv : Convex ℝ (a '' P) := hPcv.affine_image a.toAffineEquiv.toAffineMap
  have hPa0 : (0 : ℝ × ℝ) ∈ interior (a '' P) := by
    change (0 : ℝ × ℝ) ∈ interior (a.toHomeomorph '' P)
    rw [← a.toHomeomorph.image_interior]
    refine ⟨((1 / 2 : ℝ), 0), ?_, ha0⟩
    change ((1 / 2 : ℝ), 0) ∈ interior (Icc (0 : ℝ) 1 ×ˢ Icc α β)
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨hα, hβ⟩⟩
  have hfront : a '' frontier P = frontier (a '' P) := a.toHomeomorph.image_frontier P
  let d := e.symm.trans ((a.toHomeomorph.image (frontier P)).trans
    (Homeomorph.setCongr hfront))
  have hd : d.IsFinitePL := by
    obtain ⟨f, hf, hef⟩ := he.symm
    refine ⟨a ∘ f, hf.postcomp a.toContinuousAffineMap, fun x => ?_⟩
    change a (e.symm x) = a (f x)
    exact congrArg a (hef x)
  have hdheight (x : K.truncatedStarBoundary L α β) :
      (LinearMap.snd ℝ ℝ ℝ) (d x) = L x := by
    change (a (e.symm x)).2 = L x
    rw [hasnd]
    simpa only [e.apply_symm_apply] using (hheight (e.symm x)).symm
  obtain ⟨H, hH, hHheight, hHbase⟩ := hd.exists_truncatedStar_height_extension
    K hK L hα hβ hne hPa hPacv hPa0 (LinearMap.snd ℝ ℝ ℝ) hdheight
  let G := (a.toHomeomorph.image P).trans H.symm
  have hGPL : G.IsFinitePL := by
    obtain ⟨f, hf, hHf⟩ := hH.symm
    have hdomain : a.symm '' (a '' P) = P := by simp
    refine ⟨f ∘ a, ?_, fun x => ?_⟩
    · have h := hf.precomp_affineEquiv a
      rwa [hdomain] at h
    · exact hHf ⟨a x, mem_image_of_mem a x.property⟩
  refine ⟨G, hGPL, ?_, ?_⟩
  · intro x
    have h := hHheight (H.symm ⟨a x, mem_image_of_mem a x.property⟩)
    have hv : (H (H.symm ⟨a x, mem_image_of_mem a x.property⟩) : ℝ × ℝ) = a x :=
      congrArg Subtype.val (H.apply_symm_apply _)
    change (H (H.symm ⟨a x, mem_image_of_mem a x.property⟩) : ℝ × ℝ).2 =
      L (H.symm ⟨a x, mem_image_of_mem a x.property⟩) at h
    rw [hv, hasnd] at h
    exact h.symm
  · intro x
    have hxP : (x : ℝ × ℝ) ∈ P := hP.isClosed.frontier_subset x.property
    have heq : H ⟨e x, K.truncatedStarBoundary_subset_band L (hα.trans hβ).le
        (e x).property⟩ = ⟨a x, mem_image_of_mem a hxP⟩ := by
      apply Subtype.ext
      calc
        (H ⟨e x, _⟩ : ℝ × ℝ) = d (e x) := hHbase (e x)
        _ = a x := by
          change a (e.symm (e x)) = a x
          rw [e.symm_apply_apply]
    change (H.symm ⟨a x, mem_image_of_mem a hxP⟩ : E) = e x
    rw [← heq, H.symm_apply_apply]

end Homeomorph
