import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine
import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import Mathlib.Topology.MetricSpace.Thickening










set_option autoImplicit false

open Set Metric

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem FinitePiecewiseAffineOn.exists_supported_extension_of_eq_zero_off_with_vertices
    {f : E → F} {S T U : Set E} (hf : FinitePiecewiseAffineOn f S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hSK : S ⊆ K.space)
    (hT : IsCompact T) (hfzero : ∀ x ∈ S, x ∉ T → f x = 0)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (g : E → F) (R : SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.space = K.space ∧ R.AffineOnFaces g ∧
      EqOn g (S.indicator f) R.vertices ∧ EqOn g f S ∧
      (∀ x, x ∉ U → g x = 0) ∧ (∀ x, x ∉ K.space → g x = 0) := by
  classical
  obtain ⟨J, hJ, hJS, hfJ⟩ := hf
  obtain ⟨δ, hδ, hδU⟩ := hT.exists_cthickening_subset_open hU hTU
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, hLN, hLd⟩ := K.exists_finite_subdivision_mesh hK hN hδ
  let : Fintype J.faces := hJ.fintype
  choose H hH using fun t : J.faces =>
    t.val.exists_affine_halfspaces_convexHull (J.indep t.property)
  let Htotal := Finset.univ.biUnion H
  obtain ⟨R, hR, hRL, _, hRH⟩ :=
    L.exists_subdivision_respectsAffineHyperplanes hL hLN Htotal
  have hRK : R.space = K.space := hRL.space_eq.trans hLK.space_eq
  have hRd (s : Finset E) (hs : s ∈ R.faces) :
      diam (convexHull ℝ (s : Set E)) ≤ δ := by
    obtain ⟨t, ht, hst⟩ := hRL.face_subset s hs
    exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans
      (hLd t ht)
  obtain ⟨g, hg, hgv⟩ := R.exists_affineOnFaces_eqOn_vertices (S.indicator f)
  let G : E → F := K.space.indicator g
  have hG (x : E) (hx : x ∈ R.space) : G x = g x :=
    indicator_of_mem (hRK ▸ hx) g
  have hverts (s : Finset E) (hs : s ∈ R.faces) : (s : Set E) ⊆ R.vertices := by
    rw [SimplicialComplex.vertices_eq]
    exact subset_biUnion_of_mem hs
  refine ⟨G, R, hR, hRK, hg.congr (fun x hx => (hG x hx).symm), ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (hG v (R.vertices_subset_space hv)).trans (hgv hv)
  · intro x hx
    have hxR : x ∈ R.space := hRK.symm ▸ hSK hx
    rw [hG x hxR]
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp (hJS.symm ▸ hx)
    let i : J.faces := ⟨t, ht⟩
    have hHi : ∀ A ∈ H i, R.RespectsAffineHyperplane A := fun A hA =>
      hRH A (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩)
    have hxH : ∀ A ∈ H i, A x ≤ 0 := by
      change x ∈ {y | ∀ A ∈ H i, A y ≤ 0}
      rw [← hH i]
      exact hxt
    obtain ⟨s, hs, hxs, hsH⟩ := R.exists_face_in_halfspaces (H i) hHi hxR hxH
    have hst : (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
      intro v hv
      rw [hH i]
      exact hsH v hv
    have hsS : (s : Set E) ⊆ S :=
      hst.trans (fun _ hy => hJS ▸ J.convexHull_subset_space ht hy)
    obtain ⟨a, ha⟩ := hg s hs
    obtain ⟨b, hb⟩ := hfJ t ht
    have hab : EqOn a.toAffineMap b.toAffineMap (s : Set E) := by
      intro v hv
      exact (ha (subset_convexHull ℝ _ hv)).symm.trans
        ((hgv (hverts s hs hv)).trans
          ((indicator_of_mem (hsS hv) f).trans (hb (hst hv))))
    have hxold : x ∈ convexHull ℝ (t : Set E) :=
      convexHull_min hst (convex_convexHull ℝ _) hxs
    exact (ha hxs).trans
      ((AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hxs)).trans
        (hb hxold).symm)
  · intro x hxU
    by_cases hxK : x ∈ K.space
    · have hxR : x ∈ R.space := hRK.symm ▸ hxK
      rw [hG x hxR]
      obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxR
      have hzero : g '' (s : Set E) ⊆ {0} := by
        rintro _ ⟨v, hv, rfl⟩
        have hvT : v ∉ T := by
          intro hvT
          have hdist : dist x v ≤ δ :=
            (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
              hxs (subset_convexHull ℝ _ hv)).trans (hRd s hs)
          exact hxU (hδU (mem_cthickening_of_dist_le x v δ T hvT hdist))
        change g v = 0
        rw [hgv (hverts s hs hv)]
        by_cases hvS : v ∈ S
        · rw [indicator_of_mem hvS, hfzero v hvS hvT]
        · exact indicator_of_notMem hvS f
      simpa only [convexHull_singleton, mem_singleton_iff] using
        hg.mapsTo_convexHull hs hzero hxs
    · exact indicator_of_notMem hxK g
  · intro x hx
    exact indicator_of_notMem hx g





theorem FinitePiecewiseAffineOn.exists_supported_extension_of_eq_zero_off
    {f : E → F} {S T U : Set E} (hf : FinitePiecewiseAffineOn f S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hSK : S ⊆ K.space)
    (hT : IsCompact T) (hfzero : ∀ x ∈ S, x ∉ T → f x = 0)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ g : E → F, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S ∧
      (∀ x, x ∉ U → g x = 0) ∧ (∀ x, x ∉ K.space → g x = 0) := by
  obtain ⟨g, R, hR, hRK, hg, _, heq, hzeroU, hzeroK⟩ :=
    hf.exists_supported_extension_of_eq_zero_off_with_vertices K hK hSK hT hfzero hU hTU
  exact ⟨g, ⟨R, hR, hRK, hg⟩, heq, hzeroU, hzeroK⟩





theorem FinitePiecewiseAffineOn.exists_supported_extension
    {f : E → F} {S U : Set E} (hf : FinitePiecewiseAffineOn f S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hSK : S ⊆ K.space)
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ g : E → F, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S ∧
      (∀ x, x ∉ U → g x = 0) ∧ (∀ x, x ∉ K.space → g x = 0) :=
  hf.exists_supported_extension_of_eq_zero_off K hK hSK hf.isCompact
    (fun _ hx hn => False.elim (hn hx)) hU hSU

end Geometry
