import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.BoundaryConeComplex
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem exists_one_boundary_cap_triangulation
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hne : L.space.Nonempty) (hdim : ∀ s ∈ L.faces, s.card ≤ 2) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧
      J.space = (fun x : E ↦ (x, (0 : ℝ))) '' K.space ∪ boundaryCircleCap true L.space ∧
      J.surfaceEulerCount = K.surfaceEulerCount + 1 - L.surfaceEulerCount ∧
      ∀ s, s ∈ J.faces ↔
        (∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ)))) ∨
        s = {(0, (1 : ℝ))} ∨ ∃ t ∈ L.faces,
          s = insert (0, (1 : ℝ)) (t.image (fun x : E ↦ (x, (0 : ℝ)))) := by
  classical
  let z : E →ᴬ[ℝ] (E × ℝ) :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hz : Function.Injective z := fun x y hxy ↦ congrArg Prod.fst hxy
  let hf := K.affineOnFaces_affine z
  let A := hf.embeddedImage hz.injOn
  have hA : A.faces.Finite := hf.embeddedImage_finite _ hK
  have hAs : A.space = z '' K.space := hf.embeddedImage_space _
  have hL : L.faces.Finite := hK.subset hLK
  let lf := L.affineOnFaces_affine z
  let B := lf.embeddedImage hz.injOn
  have hBs : B.space = L.space ×ˢ ({0} : Set ℝ) := by
    rw [lf.embeddedImage_space]
    ext x
    exact ⟨fun ⟨y, hy, he⟩ ↦ he ▸ ⟨hy, rfl⟩,
      fun ⟨hx, hx0⟩ ↦ ⟨x.1, hx, Prod.ext rfl hx0.symm⟩⟩
  have hBA : B ≤ A := by
    intro s hs
    change s ∈ (lf.embeddedImage hz.injOn).faces at hs
    rw [lf.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    change t.image z ∈ A.faces
    rw [hf.embeddedImage_faces]
    exact ⟨t, hLK ht, rfl⟩
  obtain ⟨C, hC, hCs, _, hcountC, hbaseC, hplaneC, hfacesC⟩ :=
    exists_boundaryCircleCap_complex_with_faces true L hL hne hdim
  have hBC : B ≤ C := by
    intro s hs
    change s ∈ (lf.embeddedImage hz.injOn).faces at hs
    rw [lf.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hbaseC t ht
  have hplaneA {s : Finset (E × ℝ)} (hs : s ∈ A.faces) : ∀ x ∈ s, x.2 = 0 := by
    rw [hf.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rfl
  have hAC : A ⊓ C = B := by
    apply SimplicialComplex.ext
    ext s
    constructor
    · rintro ⟨hsA, hsC⟩
      obtain ⟨t, ht, rfl⟩ := hplaneC s hsC (hplaneA hsA)
      rw [lf.embeddedImage_faces]
      exact ⟨t, ht, rfl⟩
    · exact fun hs ↦ ⟨hBA hs, hBC hs⟩
  have hcontact : A.space ∩ C.space ⊆ B.space := by
    intro x hx
    have hx0 : x.2 = 0 := by obtain ⟨y, hy, rfl⟩ := hAs.subset hx.1; rfl
    rw [hBs]
    exact (boundaryCircleCap_plane true L.space).subset
      ⟨hCs.subset hx.2, mem_univ _, hx0⟩
  let J := A.unionOfCompatible C (fun _ hs _ ht ↦
    A.cross_inter_subset_of_common_subcomplex C B hBA hBC hcontact hs ht)
  refine ⟨J, hA.union hC, ?_, ?_, ?_⟩
  · rw [A.space_unionOfCompatible, hAs, hCs]
    rfl
  · have hc := A.surfaceEulerCount_union_add_inter C J hA hC rfl
    rw [hAC, hcountC, hf.surfaceEulerCount_embeddedImage,
      lf.surfaceEulerCount_embeddedImage] at hc
    omega
  · intro s
    have hAf : s ∈ A.faces ↔
        ∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ))) := by
      rw [hf.embeddedImage_faces]
      exact ⟨fun ⟨t, ht, he⟩ ↦ ⟨t, ht, he.symm⟩,
        fun ⟨t, ht, he⟩ ↦ ⟨t, ht, he.symm⟩⟩
    change (s ∈ A.faces ∨ s ∈ C.faces) ↔ _
    rw [hAf, hfacesC]
    simp only [capSign, if_true]
    constructor
    · rintro (h | ⟨t, ht, he⟩ | h)
      · exact Or.inl h
      · exact Or.inl ⟨t, hLK ht, he⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

end PoincareConjecture.M76.Dehn.Annuli
