import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PlanarDiskCount
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

noncomputable def AffineOnFaces.embeddedFaceEquiv (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (n : ℕ) :
    K.FaceOfCard n ≃ (hf.embeddedImage hinj).FaceOfCard n := by
  classical
  let : DecidableEq F := Classical.decEq _
  have hinjs (s : Finset E) (hs : s ∈ K.faces) : InjOn f (s : Set E) :=
    hinj.mono ((subset_convexHull ℝ _).trans (K.convexHull_subset_space hs))
  let g : K.FaceOfCard n → (hf.embeddedImage hinj).FaceOfCard n := fun s =>
    ⟨s.val.image f, (hf.embeddedImage_faces hinj) ▸ mem_image_of_mem _ s.property.1,
      (Finset.card_image_of_injOn (hinjs s.val s.property.1)).trans s.property.2⟩
  apply Equiv.ofBijective g
  constructor
  · intro s t h
    have himage : s.val.image f = t.val.image f := congrArg Subtype.val h
    apply Subtype.ext
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hy : f x ∈ t.val.image f := himage ▸ Finset.mem_image_of_mem f hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hy
      have hxy : y = x := hinj
        (K.convexHull_subset_space t.property.1 (subset_convexHull ℝ _ hy))
        (K.convexHull_subset_space s.property.1 (subset_convexHull ℝ _ hx)) heq
      exact hxy ▸ hy
    · intro hx
      have hy : f x ∈ s.val.image f := himage.symm ▸ Finset.mem_image_of_mem f hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hy
      have hxy : y = x := hinj
        (K.convexHull_subset_space s.property.1 (subset_convexHull ℝ _ hy))
        (K.convexHull_subset_space t.property.1 (subset_convexHull ℝ _ hx)) heq
      exact hxy ▸ hy
  · rintro ⟨t, ht, htcard⟩
    rw [hf.embeddedImage_faces hinj] at ht
    obtain ⟨s, hs, heq⟩ := ht
    have hcard : s.card = n :=
      (Finset.card_image_of_injOn (hinjs s hs)).symm.trans
        ((congrArg Finset.card heq).trans htcard)
    exact ⟨⟨s, hs, hcard⟩, Subtype.ext heq⟩

theorem AffineOnFaces.surfaceEulerCount_embeddedImage (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) :
    (hf.embeddedImage hinj).surfaceEulerCount = K.surfaceEulerCount := by
  unfold surfaceEulerCount
  rw [← Nat.card_congr (hf.embeddedFaceEquiv hinj 1),
    ← Nat.card_congr (hf.embeddedFaceEquiv hinj 2),
    ← Nat.card_congr (hf.embeddedFaceEquiv hinj 3)]

theorem AffineOnFaces.surfaceEulerCount_embedded_planar_disk [Nontrivial E]
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    (hdim : Module.finrank ℝ E = 2) (hK : K.faces.Finite)
    [ContractibleSpace K.space] :
    (hf.embeddedImage hinj).surfaceEulerCount = 1 := by
  rw [hf.surfaceEulerCount_embeddedImage hinj]
  exact K.surfaceEulerCount_eq_one_of_planar_contractible hdim hK

end Geometry.SimplicialComplex
