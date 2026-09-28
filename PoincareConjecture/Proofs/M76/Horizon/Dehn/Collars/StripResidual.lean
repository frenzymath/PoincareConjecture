import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.FiniteResidual
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

local notation "I" => Icc (0 : ℝ) 1

theorem exists_finite_collar_strip_residual
    (K : SimplicialComplex ℝ F) (L : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (c : E × ℝ → F) (hc : FinitePiecewiseAffineOn c (L.space ×ˢ I))
    (hinj : InjOn c (L.space ×ˢ I)) (hinside : MapsTo c (L.space ×ˢ I) K.space)
    (hopen : IsOpen ((Subtype.val : K.space → F) ⁻¹'
      (c '' (L.space ×ˢ Ico (0 : ℝ) 1)))) :
    ∃ J : SimplicialComplex ℝ F, J.faces.Finite ∧
      J.space = K.space \ c '' (L.space ×ˢ Ico (0 : ℝ) 1) ∧
      (c '' (L.space ×ˢ I)) ∪ J.space = K.space ∧
      ∀ z ∈ L.space ×ˢ I, c z ∈ J.space ↔ z.2 = 1 := by
  let O := c '' (L.space ×ˢ Ico (0 : ℝ) 1)
  let roof : E → F := fun x ↦ c (x, 1)
  let top : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 1)
  have htop : FinitePiecewiseAffineOn top L.space :=
    (L.affineOnFaces_affine top).finitePiecewiseAffineOn hL
  have hroof : FinitePiecewiseAffineOn roof L.space :=
    hc.comp htop (fun x hx ↦ ⟨hx, zero_le_one, le_rfl⟩)
  obtain ⟨C, hC, hCs⟩ := hc.exists_finite_triangulation_image
  obtain ⟨B, hB, hBs⟩ := hroof.exists_finite_triangulation_image
  have hOC : O ⊆ C.space := by
    rw [hCs]
    exact image_mono (prod_mono_right Ico_subset_Icc_self)
  have hCK : C.space ⊆ K.space := by
    rw [hCs]
    exact image_subset_iff.mpr hinside
  have hroof_eq : C.space \ O = B.space := by
    rw [hCs, hBs]
    apply Subset.antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, hyO⟩
      have hz1 : z.2 = 1 := le_antisymm hz.2.2 (not_lt.mp (fun hlt ↦
        hyO ⟨z, ⟨hz.1, hz.2.1, hlt⟩, rfl⟩))
      exact ⟨z.1, hz.1, by dsimp [roof]; rw [← hz1]⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨⟨(x, 1), ⟨hx, zero_le_one, le_rfl⟩, rfl⟩, ?_⟩
      rintro ⟨z, hz, heq⟩
      have he := hinj ⟨hz.1, hz.2.1, hz.2.2.le⟩
        ⟨hx, zero_le_one, le_rfl⟩ heq
      have hheight := congrArg Prod.snd he
      exact (ne_of_lt hz.2.2) hheight
  let : CompactSpace K.space := (isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK))
  have hclosed : IsClosed (K.space \ O) := by
    have hcompact := hopen.isClosed_compl.isCompact.image continuous_subtype_val
    have heq : (Subtype.val : K.space → F) '' (((Subtype.val : K.space → F) ⁻¹' O)ᶜ) =
        K.space \ O := by
      ext x
      simp only [mem_image, mem_compl_iff, mem_preimage, mem_sdiff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hx, hn⟩
        exact ⟨⟨x, hx⟩, hn, rfl⟩
    rw [heq] at hcompact
    exact hcompact.isClosed
  obtain ⟨J, hJ, hJs⟩ := exists_triangulation_collar_residual K C B hK hC hB
    hCK hOC hroof_eq hclosed
  refine ⟨J, hJ, hJs, ?_, ?_⟩
  · rw [hJs, ← hCs]
    apply Subset.antisymm (union_subset hCK sdiff_subset)
    intro x hx
    by_cases hxO : x ∈ O
    · exact Or.inl (hOC hxO)
    · exact Or.inr ⟨hx, hxO⟩
  · intro z hz
    rw [hJs]
    constructor
    · intro hzJ
      exact le_antisymm hz.2.2 (not_lt.mp (fun hlt ↦
        hzJ.2 ⟨z, ⟨hz.1, hz.2.1, hlt⟩, rfl⟩))
    · intro hz1
      refine ⟨hinside hz, ?_⟩
      rintro ⟨w, hw, heq⟩
      have he := hinj ⟨hw.1, hw.2.1, hw.2.2.le⟩ hz heq
      have hheight := congrArg Prod.snd he
      exact (ne_of_lt hw.2.2) (hheight.trans hz1)

end PoincareConjecture.M76.Dehn
