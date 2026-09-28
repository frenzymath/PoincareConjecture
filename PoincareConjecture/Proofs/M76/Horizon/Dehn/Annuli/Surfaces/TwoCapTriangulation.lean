import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.BoundaryConeComplex
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in



theorem exists_two_cap_triangulation_with_faces
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdimK : ∀ s ∈ K.faces, s.card ≤ 3)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ b, L b ≤ K)
    (hne : ∀ b, (L b).space.Nonempty)
    (hdimL : ∀ b s, s ∈ (L b).faces → s.card ≤ 2)
    (hdis : Disjoint (L false).space (L true).space) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧
      J.space = ((fun x : E ↦ (x, (0 : ℝ))) '' K.space ∪
        boundaryCircleCap false (L false).space) ∪ boundaryCircleCap true (L true).space ∧
      (∀ s ∈ J.faces, s.card ≤ 3) ∧
      J.surfaceEulerCount = K.surfaceEulerCount + 2 -
        (L false).surfaceEulerCount - (L true).surfaceEulerCount ∧
      (∀ s ∈ K.faces, s.image (fun x : E ↦ (x, (0 : ℝ))) ∈ J.faces) ∧
      ∀ s, s ∈ J.faces ↔
        (∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ)))) ∨
        ∃ b : Bool, s = {(0, capSign b)} ∨
          ∃ t ∈ (L b).faces, s = insert (0, capSign b)
            (t.image (fun x : E ↦ (x, (0 : ℝ)))) := by
  classical
  let z : E →ᴬ[ℝ] (E × ℝ) :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hz : Function.Injective z := fun x y hxy ↦ congrArg Prod.fst hxy
  let hf := K.affineOnFaces_affine z
  let A := hf.embeddedImage hz.injOn
  have hA : A.faces.Finite := hf.embeddedImage_finite _ hK
  have hAs : A.space = z '' K.space := hf.embeddedImage_space _
  have hdimA : ∀ s ∈ A.faces, s.card ≤ 3 := by
    intro s hs
    rw [hf.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans (hdimK t ht)
  have hLfin (b : Bool) : (L b).faces.Finite := hK.subset (hLK b)
  let lf := fun b ↦ (L b).affineOnFaces_affine z
  let B := fun b ↦ (lf b).embeddedImage hz.injOn
  have hB (b : Bool) : (B b).faces.Finite := (lf b).embeddedImage_finite _ (hLfin b)
  have hBs (b : Bool) : (B b).space = (L b).space ×ˢ ({0} : Set ℝ) := by
    rw [(lf b).embeddedImage_space]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨x.1, hx, Prod.ext rfl hx0.symm⟩
  have hBA (b : Bool) : B b ≤ A := by
    intro s hs
    change s ∈ ((lf b).embeddedImage hz.injOn).faces at hs
    rw [(lf b).embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    change t.image z ∈ A.faces
    rw [hf.embeddedImage_faces]
    exact ⟨t, hLK b ht, rfl⟩
  choose C hC hCs hdimC hcountC hbaseC hplaneC hfacesC using
    fun b ↦ exists_boundaryCircleCap_complex_with_faces b (L b) (hLfin b) (hne b) (hdimL b)
  have hBC (b : Bool) : B b ≤ C b := by
    intro s hs
    change s ∈ ((lf b).embeddedImage hz.injOn).faces at hs
    rw [(lf b).embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hbaseC b t ht
  have hplaneA {s : Finset (E × ℝ)} (hs : s ∈ A.faces) : ∀ x ∈ s, x.2 = 0 := by
    rw [hf.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rfl
  have hAC (b : Bool) : A ⊓ C b = B b := by
    apply SimplicialComplex.ext
    ext s
    constructor
    · rintro ⟨hsA, hsC⟩
      obtain ⟨t, ht, rfl⟩ := hplaneC b s hsC (hplaneA hsA)
      rw [(lf b).embeddedImage_faces]
      exact ⟨t, ht, rfl⟩
    · exact fun hs ↦ ⟨hBA b hs, hBC b hs⟩
  have hcontact (b : Bool) : A.space ∩ (C b).space ⊆ (B b).space := by
    intro x hx
    have hx0 : x.2 = 0 := by
      obtain ⟨y, hy, rfl⟩ := hAs.subset hx.1
      rfl
    rw [hBs]
    exact (boundaryCircleCap_plane b (L b).space).subset
      ⟨(hCs b).subset hx.2, mem_univ _, hx0⟩
  let U := A.unionOfCompatible (C false) (fun _ hs _ ht ↦
    A.cross_inter_subset_of_common_subcomplex (C false) (B false)
      (hBA false) (hBC false) (hcontact false) hs ht)
  have hU : U.faces.Finite := hA.union (hC false)
  have hUs : U.space = A.space ∪ (C false).space := A.space_unionOfCompatible _ _
  have hBU : B true ≤ U := fun s hs ↦ Or.inl (hBA true hs)
  have hCdis : Disjoint (C false).space (C true).space := by
    rw [hCs false, hCs true]
    exact boundaryCircleCaps_disjoint hdis
  have hcontact1 : U.space ∩ (C true).space ⊆ (B true).space := by
    intro x hx
    rcases hUs.subset hx.1 with hxA | hxC
    · exact hcontact true ⟨hxA, hx.2⟩
    · exact (disjoint_left.mp hCdis hxC hx.2).elim
  let J := U.unionOfCompatible (C true) (fun _ hs _ ht ↦
    U.cross_inter_subset_of_common_subcomplex (C true) (B true)
      hBU (hBC true) hcontact1 hs ht)
  have hUC : U ⊓ C true = B true := by
    apply SimplicialComplex.ext
    ext s
    constructor
    · rintro ⟨hsU, hsC⟩
      rcases hsU with hsA | hs0
      · exact (show s ∈ (A ⊓ C true).faces from ⟨hsA, hsC⟩) |> (hAC true ▸ ·)
      · obtain ⟨p, hp⟩ := (C false).nonempty_of_mem_faces hs0
        exact (disjoint_left.mp hCdis ((C false).subset_space hs0 hp)
          ((C true).subset_space hsC hp)).elim
    · exact fun hs ↦ ⟨hBU hs, hBC true hs⟩
  refine ⟨J, hU.union (hC true), ?_, ?_, ?_, ?_, ?_⟩
  · rw [U.space_unionOfCompatible, hUs, hAs, hCs false, hCs true]
    rfl
  · rintro s ((hs | hs) | hs)
    · exact hdimA s hs
    · exact hdimC false s hs
    · exact hdimC true s hs
  · have hcount0 := A.surfaceEulerCount_union_add_inter (C false) U hA (hC false) rfl
    have hcount1 := U.surfaceEulerCount_union_add_inter (C true) J hU (hC true) rfl
    rw [hAC false, hcountC false] at hcount0
    rw [hUC, hcountC true] at hcount1
    have hAE : A.surfaceEulerCount = K.surfaceEulerCount := hf.surfaceEulerCount_embeddedImage _
    have hBE (b : Bool) : (B b).surfaceEulerCount = (L b).surfaceEulerCount :=
      (lf b).surfaceEulerCount_embeddedImage _
    rw [hAE, hBE false] at hcount0
    rw [hBE true] at hcount1
    omega
  · intro s hs
    apply Or.inl (Or.inl ?_)
    rw [hf.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  · intro s
    have hAfaces : s ∈ A.faces ↔
        ∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ))) := by
      rw [hf.embeddedImage_faces]
      exact ⟨fun ⟨t, ht, he⟩ ↦ ⟨t, ht, he.symm⟩,
        fun ⟨t, ht, he⟩ ↦ ⟨t, ht, he.symm⟩⟩
    change (s ∈ A.faces ∨ s ∈ (C false).faces) ∨ s ∈ (C true).faces ↔ _
    rw [hAfaces, hfacesC false, hfacesC true]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · rcases h with ⟨t, ht, he⟩ | h
        · exact Or.inl ⟨t, hLK false ht, he⟩
        · exact Or.inr ⟨false, h⟩
      · rcases h with ⟨t, ht, he⟩ | h
        · exact Or.inl ⟨t, hLK true ht, he⟩
        · exact Or.inr ⟨true, h⟩
    · rintro (h | ⟨b, h⟩)
      · exact Or.inl (Or.inl h)
      · cases b
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr h)

open Classical in

theorem exists_two_cap_triangulation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdimK : ∀ s ∈ K.faces, s.card ≤ 3)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ b, L b ≤ K)
    (hne : ∀ b, (L b).space.Nonempty)
    (hdimL : ∀ b s, s ∈ (L b).faces → s.card ≤ 2)
    (hdis : Disjoint (L false).space (L true).space) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧
      J.space = ((fun x : E ↦ (x, (0 : ℝ))) '' K.space ∪
        boundaryCircleCap false (L false).space) ∪ boundaryCircleCap true (L true).space ∧
      (∀ s ∈ J.faces, s.card ≤ 3) ∧
      J.surfaceEulerCount = K.surfaceEulerCount + 2 -
        (L false).surfaceEulerCount - (L true).surfaceEulerCount ∧
      ∀ s ∈ K.faces, s.image (fun x : E ↦ (x, (0 : ℝ))) ∈ J.faces := by
  obtain ⟨J, hJ, hJs, hdimJ, hcount, hfaces, _⟩ :=
    exists_two_cap_triangulation_with_faces K hK hdimK L hLK hne hdimL hdis
  exact ⟨J, hJ, hJs, hdimJ, hcount, hfaces⟩

end PoincareConjecture.M76.Dehn.Annuli
