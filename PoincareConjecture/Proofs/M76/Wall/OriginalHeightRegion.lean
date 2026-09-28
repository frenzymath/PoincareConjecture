import PoincareConjecture.Proofs.M76.Wall.Mathlib.SelectedStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Classical in





theorem original_exterior_height_region
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    {C L W : Set X} (hL : IsClosed L) (hLC : L ⊆ C)
    (H : C ≃ₜ K.space) (g : E → C) (hgc : ContinuousOn g K.space)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (hN : N.space = F '' (C \ interior L))
    (A : Set E) {f : E → ℝ} (hf : K.AffineOnFaces f)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (hstars : ∀ p ∈ K.vertices, p ∈ A →
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (interior C ∩ W))
    {beta : ℝ} (hbeta : 0 < beta) :
    let D := (fun z => (g z : X)) '' (N.space ∩ {z | beta ≤ f z})
    IsCompact D ∧ D ⊆ interior C ∩ W ∧
      D = (C \ interior L) ∩ {y | beta ≤ f (F y)} ∧
      D ∩ L = frontier L ∩ {y | beta ≤ f (F y)} := by
  classical
  let D := (fun z => (g z : X)) '' (N.space ∩ {z | beta ≤ f z})
  change IsCompact D ∧ D ⊆ interior C ∩ W ∧
    D = (C \ interior L) ∩ {y | beta ≤ f (F y)} ∧
    D ∩ L = frontier L ∩ {y | beta ≤ f (F y)}
  have hNKs : N.space ⊆ K.space := space_subset_of_le hNK
  have hgF (y : X) (hy : y ∈ C) : (g (F y) : X) = y := by
    have h := hg (H ⟨y, hy⟩)
    rw [H.symm_apply_apply] at h
    simpa only [hHF] using h
  have hD : D = (C \ interior L) ∩ {y | beta ≤ f (F y)} := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzN, hzf⟩, rfl⟩
      obtain ⟨t, ht, htz⟩ := hN.subset hzN
      change (g z : X) ∈ (C \ interior L) ∩ {y | beta ≤ f (F y)}
      rw [← htz, hgF t ht.1]
      refine ⟨ht, ?_⟩
      change beta ≤ f (F t)
      rw [htz]
      exact hzf
    · rintro ⟨hy, hyf⟩
      exact ⟨F y, ⟨hN.symm.subset (mem_image_of_mem F hy), hyf⟩, hgF y hy.1⟩
  have hcompact : IsCompact D := by
    let : CompactSpace N.space := isCompact_iff_compactSpace.mp
      (N.isCompact_space_of_finite (hK.subset hNK))
    let T : Set N.space := {z | beta ≤ f z}
    have hT : IsClosed T := isClosed_Ici.preimage
      ((hf.continuousOn hK).mono hNKs).domRestrict
    have hcont : Continuous (fun z : N.space => (g z : X)) :=
      continuous_subtype_val.comp ((hgc.mono hNKs).domRestrict)
    have himage : (fun z : N.space => (g z : X)) '' T = D := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ⟨z.property, hz⟩, rfl⟩
      · rintro ⟨z, ⟨hzN, hzf⟩, rfl⟩
        exact ⟨⟨z, hzN⟩, hzf, rfl⟩
    rw [← himage]
    exact hT.isCompact.image hcont
  refine ⟨hcompact, ?_, hD, ?_⟩
  · rintro y ⟨z, ⟨hzN, hzf⟩, rfl⟩
    obtain ⟨p, hpK, hpA, O, _, hzO, hOS⟩ :=
      K.exists_selected_star_neighborhood hK hf A hzero ⟨z, hNKs hzN⟩
        (hbeta.trans_le hzf).ne'
    exact hstars p hpK hpA (hOS (mem_image_of_mem Subtype.val hzO))
  · rw [hD]
    ext y
    constructor
    · rintro ⟨⟨hy, hyf⟩, hyL⟩
      exact ⟨⟨subset_closure hyL, hy.2⟩, hyf⟩
    · rintro ⟨hyfront, hyf⟩
      have hyL := hL.frontier_subset hyfront
      exact ⟨⟨⟨hLC hyL, hyfront.2⟩, hyf⟩, hyL⟩

end PoincareConjecture.M76
