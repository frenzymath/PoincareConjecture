import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryChartCover
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRelativeCornerChart
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLRegularLevels
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.AffineLevelSubcomplex

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_compact_PL_relative_regular_level
    {M E ι : Type*} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {w : M → ℝ} (hw : Continuous w)
    (hwPL : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    {Q R : Set M} (hQ : IsCompact Q) (hzero : ∀ x, x ∉ Q → w x = 0)
    (hR : IsClosed R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (u : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear u = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ psi (B y))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ t ∈ Ioo a b,
      IsCompact {x | t ≤ w x} ∧ IsCompact {x | x ∈ R ∧ t ≤ w x} ∧
      (∀ x : M, w x = t →
        ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (H : OpenPartialHomeomorph M E),
          ell.contLinear v = 1 ∧ x ∈ H.source ∧
          (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E) ∧
          ∀ y ∈ H.source, ell (H y) = w y) ∧
      ∀ x ∈ frontier R, w x = t →
        ∃ (psi ell : E →ᴬ[ℝ] ℝ) (u v : E) (C : OpenPartialHomeomorph M E),
          psi.contLinear u = 1 ∧ psi.contLinear v = 0 ∧ ell.contLinear v = 1 ∧
          x ∈ C.source ∧ psi (C x) = 0 ∧ ell (C x) = 0 ∧
          (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid E) ∧
          (∀ y ∈ C.source, (y ∈ R ∧ t ≤ w y) ↔ 0 ≤ psi (C y)) ∧
          (∀ y ∈ C.source,
            (y ∈ frontier R ∧ t ≤ w y) ↔ (psi (C y) = 0 ∧ 0 ≤ ell (C y))) ∧
          ∀ y ∈ C.source,
            (w y = t ∧ y ∈ R) ↔ (psi (C y) = 0 ∧ ell (C y) ≤ 0) := by
  classical
  have hbandQ : w ⁻¹' Icc a b ⊆ Q := by
    intro x hx
    by_contra hxQ
    have hax : a ≤ w x := hx.1
    rw [hzero x hxQ] at hax
    exact (not_le_of_gt ha) hax
  have hband : IsCompact (w ⁻¹' Icc a b) :=
    hQ.of_isClosed_subset (isClosed_Icc.preimage hw) hbandQ
  let S : Set M := (w ⁻¹' Icc a b) ∩ frontier R
  have hS : IsCompact S := hband.inter_right isClosed_frontier
  obtain ⟨s, B, psi, u, K, hnorm, hK, _, hfK, halign, hBPL, hBR, hcoverB⟩ :=
    exists_finite_PL_boundary_chart_cover e hcover hwPL hS inter_subset_right hboundary
  let Z : Set ℝ := ⋃ i : s, (w ∘ (B i).symm) '' (K i).vertices
  have hZ : Z.Finite := finite_iUnion fun i =>
    ((K i).finite_vertices_of_finite_faces (hK i)).image _
  obtain ⟨z, hz, hzZ⟩ := (Ioo_infinite hab).exists_notMem_finite hZ
  have hopen : IsOpen (Ioo a b \ Z) := isOpen_Ioo.inter hZ.isClosed.isOpen_compl
  obtain ⟨l, r, hlr, hsub⟩ := hopen.exists_Ioo_subset ⟨z, hz, hzZ⟩
  let m : ℝ := (l + r) / 2
  have hml : l < m := by dsimp only [m]; linarith
  have hmr : m < r := by dsimp only [m]; linarith
  have hm0 : 0 < m := ha.trans (hsub ⟨hml, hmr⟩).1.1
  obtain ⟨t, ht, hNt, hcharts⟩ := exists_compact_PL_regular_superlevel
    e hcompat hcover hw hwPL hQ hzero hm0 hmr
  have htZ : t ∈ Ioo a b \ Z := hsub ⟨hml.trans ht.1, ht.2⟩
  refine ⟨t, htZ.1, hNt, hNt.inter_left hR, hcharts, ?_⟩
  intro x hxR hxt
  have hxS : x ∈ S := by
    refine ⟨?_, hxR⟩
    change w x ∈ Icc a b
    rw [hxt]
    exact ⟨htZ.1.1.le, htZ.1.2.le⟩
  obtain ⟨i, hxB, hxK⟩ := hcoverB x hxS
  have hlin : (psi i).toAffineMap.linear ≠ 0 := by
    intro hlinzero
    have huvalue : (psi i).toAffineMap.linear (u i) = 1 := hnorm i
    rw [hlinzero, LinearMap.zero_apply] at huvalue
    exact zero_ne_one huvalue
  have himage : (B i).IsImage (frontier R) {z | psi i z = 0} :=
    (B i).isImage_frontier_of_affine_nonneg (psi i) hlin (hBR i)
  have hxpsi : psi i (B i x) = 0 := (himage.apply_mem_iff hxB).mpr hxR
  have hheight : (w ∘ (B i).symm) (B i x) = t := by
    change w ((B i).symm (B i x)) = t
    rw [(B i).left_inv hxB, hxt]
  have hreg : ∀ z ∈ (K i).vertices,
      (w ∘ (B i).symm) z ≠ (w ∘ (B i).symm) (B i x) := by
    intro z hzK heq
    apply htZ.2
    exact mem_iUnion.mpr ⟨i, z, hzK, heq.trans hheight⟩
  let L := (K i).affineZeroSubcomplex (psi i).toAffineMap
  have hLs : L.space = (K i).space ∩ {z | psi i z = 0} :=
    (K i).affineZeroSubcomplex_space (psi i).toAffineMap (halign i)
  have hLK : L ≤ K i := fun _ hs => hs.1
  have hxL : B i x ∈ L.space := by
    rw [hLs]
    exact ⟨interior_subset hxK, hxpsi⟩
  have hLzero : ∀ z ∈ L.space, psi i z = 0 := by
    intro z hzL
    rw [hLs] at hzL
    exact hzL.2
  obtain ⟨ell, v, T, hellv, hpsiv, hellx, hxT, hTx, _, hTPL, hquad, hold, hnew⟩ :=
    (K i).exists_nonvertex_relative_corner_chart (hK i) (hfK i) hxK hreg
      L hLK hxL (psi i) hLzero (u i) (hnorm i)
  let C := (B i).trans T
  have hfy (y : M) (hy : y ∈ (B i).source) :
      (w ∘ (B i).symm) (B i y) = w y := by
    change w ((B i).symm (B i y)) = w y
    rw [(B i).left_inv hy]
  refine ⟨psi i, ell, u i, v, C, hnorm i, hpsiv, hellv, ⟨hxB, hxT⟩, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · change psi i (T (B i x)) = 0
    rw [hTx]
    exact hxpsi
  · change ell (T (B i x)) = 0
    rw [hTx]
    exact hellx
  · intro j
    change (e j).symm.trans ((B i).trans T) ∈ piecewiseAffineGroupoid E
    rw [← trans_assoc]
    exact (piecewiseAffineGroupoid E).trans (hBPL i j) hTPL
  · intro y hy
    change (y ∈ R ∧ t ≤ w y) ↔ 0 ≤ psi i (T (B i y))
    simpa only [hheight, hfy y hy.1, (hBR i y hy.1).symm] using hquad (B i y) hy.2
  · intro y hy
    have hyfront : psi i (B i y) = 0 ↔ y ∈ frontier R := himage.apply_mem_iff hy.1
    change (y ∈ frontier R ∧ t ≤ w y) ↔
      (psi i (T (B i y)) = 0 ∧ 0 ≤ ell (T (B i y)))
    simpa only [hheight, hfy y hy.1, hyfront] using hold (B i y) hy.2
  · intro y hy
    change (w y = t ∧ y ∈ R) ↔
      (psi i (T (B i y)) = 0 ∧ ell (T (B i y)) ≤ 0)
    simpa only [hheight, hfy y hy.1, (hBR i y hy.1).symm] using hnew (B i y) hy.2

end OpenPartialHomeomorph
