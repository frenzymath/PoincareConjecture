import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNonvertexHeightChart
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_compact_PL_regular_superlevel
    {M E ι : Type*} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {w : M → ℝ} (hw : Continuous w)
    (hwPL : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    {C : Set M} (hC : IsCompact C) (hzero : ∀ x, x ∉ C → w x = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ t ∈ Ioo a b, IsCompact {x | t ≤ w x} ∧
      ∀ x : M, w x = t →
        ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (H : OpenPartialHomeomorph M E),
          ell.contLinear v = 1 ∧ x ∈ H.source ∧
          (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E) ∧
          ∀ y ∈ H.source, ell (H y) = w y := by
  classical
  let S : Set M := w ⁻¹' Icc a b
  have hSC : S ⊆ C := by
    intro x hx
    by_contra hxc
    have hax : a ≤ w x := hx.1
    rw [hzero x hxc] at hax
    exact (not_le_of_gt ha) hax
  have hS : IsCompact S := hC.of_isClosed_subset (isClosed_Icc.preimage hw) hSC
  have hchoose (x : S) : ∃ (i : ι) (K : SimplicialComplex ℝ E),
      K.faces.Finite ∧ (x : M) ∈ (e i).source ∧
      e i x ∈ interior K.space ∧ K.space ⊆ (e i).target ∧
      K.AffineOnFaces (w ∘ (e i).symm) := by
    obtain ⟨i, hxi⟩ := hcover x
    obtain ⟨K, hK, hxK, hKt, hfK⟩ := hwPL i (e i x) ((e i).mapsTo hxi)
    exact ⟨i, K, hK, hxi, hxK, hKt, hfK⟩
  choose i K hK hsource hxK hKt hfK using hchoose
  let V : S → Set M := fun x => (e (i x)).source ∩ (e (i x)) ⁻¹' interior (K x).space
  have hV (x : S) : IsOpen (V x) :=
    (e (i x)).continuousOn_toFun.isOpen_inter_preimage (e (i x)).open_source isOpen_interior
  have hxV (x : S) : (x : M) ∈ V x := ⟨hsource x, hxK x⟩
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let F : Set ℝ := ⋃ x ∈ s, (w ∘ (e (i x)).symm) '' (K x).vertices
  have hF : F.Finite := s.finite_toSet.biUnion fun x _ =>
    ((K x).finite_vertices_of_finite_faces (hK x)).image _
  obtain ⟨t, ht, htF⟩ := (Ioo_infinite hab).exists_notMem_finite hF
  have ht0 : 0 < t := ha.trans ht.1
  have hlevelC : {x | t ≤ w x} ⊆ C := by
    intro x hx
    by_contra hxc
    have htx : t ≤ w x := hx
    rw [hzero x hxc] at htx
    exact (not_le_of_gt ht0) htx
  refine ⟨t, ht, hC.of_isClosed_subset (isClosed_le continuous_const hw) hlevelC, ?_⟩
  intro x hxt
  have hxS : x ∈ S := by
    change w x ∈ Icc a b
    rw [hxt]
    exact ⟨ht.1.le, ht.2.le⟩
  obtain ⟨q, hqs, hxq⟩ := mem_iUnion₂.mp (hs hxS)
  have hheight : (w ∘ (e (i q)).symm) (e (i q) x) = t := by
    change w ((e (i q)).symm (e (i q) x)) = t
    rw [(e (i q)).left_inv hxq.1, hxt]
  have hreg : ∀ z ∈ (K q).vertices,
      (w ∘ (e (i q)).symm) z ≠ (w ∘ (e (i q)).symm) (e (i q) x) := by
    intro z hz heq
    apply htF
    exact mem_iUnion₂.mpr ⟨q, hqs, z, hz, heq.trans hheight⟩
  obtain ⟨ell, v, H, hell, hxH, _, _, _, hHPL, hHheight⟩ :=
    (K q).exists_nonvertex_height_chart (hK q) (hfK q) hxq.2 hreg
  let T := (e (i q)).trans H
  refine ⟨ell, v, T, hell, ⟨hxq.1, hxH⟩, ?_, ?_⟩
  · intro j
    change (e j).symm.trans ((e (i q)).trans H) ∈ piecewiseAffineGroupoid E
    rw [← OpenPartialHomeomorph.trans_assoc]
    exact (piecewiseAffineGroupoid E).trans (hcompat j (i q)) hHPL
  · intro y hy
    change ell (H (e (i q) y)) = w y
    rw [hHheight (e (i q) y) hy.2]
    change w ((e (i q)).symm (e (i q) y)) = w y
    rw [(e (i q)).left_inv hy.1]

end OpenPartialHomeomorph
