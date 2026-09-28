import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine
import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolationBound
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_relative_finitePL_approximation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : ContinuousOn f K.space) {S : Set E}
    (hSK : S ⊆ K.space) (hfS : FinitePiecewiseAffineOn f S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E → F) (R : SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧ R.AffineOnFaces g ∧
      EqOn g f R.vertices ∧ EqOn g f S ∧
      ∀ x ∈ K.space, ‖g x - f x‖ < ε := by
  classical
  have huc := (K.isCompact_space_of_finite hK).uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (half_pos hε)
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, hLN, hLd⟩ :=
    K.exists_finite_subdivision_mesh hK hN (half_pos hδ)
  obtain ⟨J, hJ, hJS, hfJ⟩ := hfS
  let : Fintype J.faces := hJ.fintype
  choose H hH using fun t : J.faces =>
    t.val.exists_affine_halfspaces_convexHull (J.indep t.property)
  let Htotal := Finset.univ.biUnion H
  obtain ⟨R, hR, hRL, _, hRH⟩ :=
    L.exists_subdivision_respectsAffineHyperplanes hL hLN Htotal
  have hRK : R.IsSubdivision K := hRL.trans hLK
  have hRd (s : Finset E) (hs : s ∈ R.faces) :
      diam (convexHull ℝ (s : Set E)) ≤ δ / 2 := by
    obtain ⟨t, ht, hst⟩ := hRL.face_subset s hs
    exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans
      (hLd t ht)
  obtain ⟨g, hg, hgv⟩ := R.exists_affineOnFaces_eqOn_vertices f
  have hverts (s : Finset E) (hs : s ∈ R.faces) : (s : Set E) ⊆ R.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs
  refine ⟨g, R, hR, hRK, hg, hgv, ?_, ?_⟩
  · intro x hx
    have hxR : x ∈ R.space := hRK.space_eq.symm ▸ hSK hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp (hJS.symm ▸ hx)
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
    obtain ⟨a, ha⟩ := hg s hs
    obtain ⟨b, hb⟩ := hfJ t ht
    have hab : EqOn a.toAffineMap b.toAffineMap (s : Set E) := by
      intro v hv
      exact (ha (subset_convexHull ℝ _ hv)).symm.trans
        ((hgv (hverts s hs hv)).trans (hb (hst hv)))
    have hxold : x ∈ convexHull ℝ (t : Set E) :=
      convexHull_min hst (convex_convexHull ℝ _) hxs
    exact (ha hxs).trans
      ((AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hxs)).trans
        (hb hxold).symm)
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hRK.space_eq.symm ▸ hx)
    apply lt_of_le_of_lt (hg.norm_sub_le_of_vertex_bound hs hxs (f x) ?_)
      (half_lt_self hε)
    intro v hv
    have hvR := hverts s hs hv
    have hvK : v ∈ K.space := hRK.space_eq ▸ R.vertices_subset_space hvR
    have hdist : dist v x < δ :=
      ((dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
        (subset_convexHull ℝ _ hv) hxs).trans (hRd s hs)).trans_lt (half_lt_self hδ)
    rw [hgv hvR]
    exact (show ‖f v - f x‖ < ε / 2 from
      by simpa only [dist_eq_norm] using hδf v hvK x hx hdist).le

theorem exists_relative_finitePL_approximation_in_open
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : ContinuousOn f K.space) {S : Set E}
    (hSK : S ⊆ K.space) (hfS : FinitePiecewiseAffineOn f S)
    {W : Set F} (hW : IsOpen W) (hfW : MapsTo f K.space W) :
    ∃ g : E → F, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S ∧
      ∀ x ∈ K.space, segment ℝ (f x) (g x) ⊆ W := by
  have himage : IsCompact (f '' K.space) :=
    (K.isCompact_space_of_finite hK).image_of_continuousOn hf
  have hsub : f '' K.space ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfW hx
  obtain ⟨ρ, hρ, hρW⟩ := himage.exists_thickening_subset_open hW hsub
  obtain ⟨g, R, hR, hRK, hg, _, hgS, herr⟩ :=
    K.exists_relative_finitePL_approximation hK hf hSK hfS hρ
  refine ⟨g, ⟨R, hR, hRK.space_eq, hg⟩, hgS, ?_⟩
  intro x hx
  have hsegment : segment ℝ (f x) (g x) ⊆ ball (f x) ρ :=
    (convex_ball (f x) ρ).segment_subset (mem_ball_self hρ)
      (by simpa only [mem_ball, dist_eq_norm] using herr x hx)
  intro y hy
  exact hρW (mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx, hsegment hy⟩)

end Geometry.SimplicialComplex
