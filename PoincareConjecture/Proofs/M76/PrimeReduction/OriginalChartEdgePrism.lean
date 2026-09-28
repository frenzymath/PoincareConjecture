import PoincareConjecture.Proofs.M76.PrimeReduction.Mathlib.NormalizedEdgeCoordinates
import PoincareConjecture.Proofs.M76.PrimeReduction.WholeEdgePrism
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import Mathlib.Topology.OpenPartialHomeomorph.Basic










set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

private theorem exists_finite_original_edge_prism {l u r : ℝ}
    (hlu : l < u) (hr : 0 < r) :
    ∃ K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ),
      K.faces.Finite ∧ K.space = originalEdgePrism l u r := by
  have hrr : -r < r := neg_lt_self hr
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hIs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc hrr
  obtain ⟨L, hL, hLs⟩ := I.exists_finite_interval_product hI hrr
  obtain ⟨K, hK, hKs⟩ := L.exists_finite_interval_product hL hlu
  exact ⟨K, hK, by simpa only [hLs, hIs, originalEdgePrism] using hKs⟩






theorem exists_original_chart_edge_prism
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (hdim : finrank ℝ E = 3) (B : OpenPartialHomeomorph X E)
    {S U : Set X} (hS : IsClosed S) (hU : IsOpen U)
    (p q : E) (hpq : p ≠ q)
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p q t ∈ B.target)
    (hpS : B.symm p ∉ S) (hqS : B.symm q ∉ S)
    (haxis : ∀ t ∈ Ioo (0 : ℝ) 1, B.symm (AffineMap.lineMap p q t) ∈ U) :
    ∃ (F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (l u r : ℝ)
      (J : SimplicialComplex ℝ E),
      (∀ t : ℝ, F ((0, 0), t) = AffineMap.lineMap p q t) ∧
      0 < l ∧ l < u ∧ u < 1 ∧ r ∈ Ioo (0 : ℝ) 1 ∧
      J.faces.Finite ∧ J.space = F '' originalEdgePrism l u r ∧
      Convex ℝ J.space ∧ J.space ⊆ B.target ∧ B.symm '' J.space ⊆ U ∧
      (∀ t ∈ Icc (0 : ℝ) 1, B.symm (AffineMap.lineMap p q t) ∈ S →
        t ∈ Ioo l u ∧ AffineMap.lineMap p q t ∈ interior J.space) ∧
      (∀ z ∈ originalEdgePrism l u r, z.2 = l ∨ z.2 = u →
        B.symm (F z) ∉ S) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        AffineMap.lineMap p q t ∈ frontier J.space ↔ t = l ∨ t = u) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        AffineMap.lineMap p q t ∈ frontier J.space →
          B.symm (AffineMap.lineMap p q t) ∉ S := by
  obtain ⟨F, hF⟩ := ContinuousAffineEquiv.exists_normalized_edge_coordinates hdim p q hpq
  obtain ⟨C, hC, hCe⟩ := continuousOn_iff_isClosed.mp B.symm.continuousOn S hS
  have hCiff {x : E} (hx : x ∈ B.target) : x ∈ C ↔ B.symm x ∈ S := by
    constructor
    · intro h
      exact (hCe.symm.subset ⟨h, hx⟩).1
    · intro h
      exact (hCe.subset ⟨h, hx⟩).1
  let Z := F ⁻¹' C
  let W := F ⁻¹' (B.target ∩ B.symm ⁻¹' U)
  have hZ : IsClosed Z := hC.preimage F.continuous
  have hW : IsOpen W := (B.isOpen_inter_preimage_symm hU).preimage F.continuous
  have hzero : ((0, 0), (0 : ℝ)) ∉ Z := by
    intro h
    have hc : B.symm (AffineMap.lineMap p q (0 : ℝ)) ∈ S :=
      (hCiff (htarget 0 (by simp))).mp (by simpa only [Z, mem_preimage, hF] using h)
    exact hpS (by simpa using hc)
  have hone : ((0, 0), (1 : ℝ)) ∉ Z := by
    intro h
    have hc : B.symm (AffineMap.lineMap p q (1 : ℝ)) ∈ S :=
      (hCiff (htarget 1 (by simp))).mp (by simpa only [Z, mem_preimage, hF] using h)
    exact hqS (by simpa using hc)
  have hWa (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ((0, 0), t) ∈ W := by
    change F ((0, 0), t) ∈ B.target ∩ B.symm ⁻¹' U
    rw [hF]
    exact ⟨htarget t ⟨ht.1.le, ht.2.le⟩, haxis t ht⟩
  obtain ⟨l, u, r, hl, hlu, hu, hr, hKW, hcontacts, hcaps, hint, hfront⟩ :=
    exists_whole_original_edge_prism hZ hW hzero hone hWa
  obtain ⟨K, hK, hKs⟩ := exists_finite_original_edge_prism hlu hr.1
  obtain ⟨J, hJ, hJs, _⟩ :=
    (K.affineOnFaces_affine F.toContinuousAffineMap).exists_finite_triangulation_image hK
  have hwhole : J.space = F '' originalEdgePrism l u r := by
    change J.space = F '' K.space at hJs
    simpa only [hKs] using hJs
  have hconv : Convex ℝ (originalEdgePrism l u r) :=
    ((convex_Icc (-r) r).prod (convex_Icc (-r) r)).prod (convex_Icc l u)
  have hJB : J.space ⊆ B.target := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := hwhole.subset hx
    exact (hKW hz).1
  have himageFront : F '' frontier (originalEdgePrism l u r) =
      frontier (F '' originalEdgePrism l u r) := F.toHomeomorph.image_frontier _
  have himageInt : F '' interior (originalEdgePrism l u r) =
      interior (F '' originalEdgePrism l u r) := F.toHomeomorph.image_interior _
  have hJfront (z : (ℝ × ℝ) × ℝ) :
      F z ∈ frontier J.space ↔ z ∈ frontier (originalEdgePrism l u r) := by
    rw [hwhole, ← himageFront]
    exact F.injective.mem_set_image
  have hlineZ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (htS : B.symm (AffineMap.lineMap p q t) ∈ S) : ((0, 0), t) ∈ Z := by
    change F ((0, 0), t) ∈ C
    rw [hF]
    exact (hCiff (htarget t ht)).mpr htS
  refine ⟨F, l, u, r, J, hF, hl, hlu, hu, hr, hJ, hwhole, ?_, hJB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwhole]
    exact Convex.affine_image F.toAffineEquiv.toAffineMap hconv
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hwhole.subset hy
    exact (hKW hz).2
  · intro t ht htS
    have hz := hlineZ t ht htS
    refine ⟨hcontacts t ht hz, ?_⟩
    rw [hwhole, ← himageInt, ← hF t]
    exact mem_image_of_mem F (hint t ht hz)
  · intro z hz hcap hzS
    apply disjoint_left.mp hcaps ⟨hz, hcap⟩
    exact (hCiff (hKW hz).1).mpr hzS
  · intro t ht
    rw [← hF t, hJfront]
    exact hfront t ht
  · intro t ht htfront htS
    have hlt := hcontacts t ht (hlineZ t ht htS)
    have hb : t = l ∨ t = u :=
      (hfront t ht).mp ((hJfront ((0, 0), t)).mp (by simpa only [hF] using htfront))
    rcases hb with rfl | rfl
    · exact (lt_irrefl _) hlt.1
    · exact (lt_irrefl _) hlt.2

end PoincareConjecture.M76
