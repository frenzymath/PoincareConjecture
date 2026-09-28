import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CommonCornerCaps














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_reflex_corner_faces
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {K : Set AnnulusCoordinates}
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ K ↔ z.1 ≤ 0 ∨ z.2 ≤ 0)
    {T : ℝ} (hT : 0 < T) :
    ∃ (r : ℝ) (face : Fin 3 → SmoothFace AnnulusCoordinates)
      (W : Set AnnulusCoordinates),
      0 < r ∧ r ≤ T ∧ (∀ i, (face i).carrier ⊆ K) ∧
      IsOpen W ∧ H 0 ∈ W ∧ W ∩ K ⊆ ⋃ i, (face i).carrier ∧
      EqOn ((face 0).boundary 2).map ((face 1).boundary 2).map (Icc (0 : ℝ) 1) ∧
      EqOn ((face 0).boundary 1).map ((face 2).boundary 1).map (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ((face 1).boundary 1).map t = H (0, t * r)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ((face 2).boundary 2).map t = H (t * r, 0)) ∧
      (∀ t : ℝ, ((face 0).boundary 0).map t =
        (1 - t) • H (-r, 0) + t • H (0, -r)) ∧
      (∀ t : ℝ, ((face 1).boundary 0).map t =
        (1 - t) • H (-r, 0) + t • H (0, r)) ∧
      (∀ t : ℝ, ((face 2).boundary 0).map t =
        (1 - t) • H (r, 0) + t • H (0, -r)) ∧
      (∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
        (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        convexHull ℝ (range b) ⊆ C.source ∧
        (face i).carrier = C '' convexHull ℝ (range b) ∧
        ∀ k, ((face i).boundary k).map = C ∘
          affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hside
  let J := H.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := ⟨h0, mem_ball_self hR⟩
  have hJ : ContDiffOn ℝ ∞ J J.source := hH.mono (fun _ hz => hz.1)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target := hHi.mono (fun _ hz => hz.1)
  obtain ⟨r, F, W, hr, hrT, hW, hpW, hWt, hsub, hcover, hsecond, hfirst,
    hchord, _, hfirstEq, hsecondEq, hcoordinates⟩ :=
      m64Intrinsic_exists_four_corner_faces J hJ0 hJ hJi hT
  let idx : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
  let face (i : Fin 3) := F (idx i)
  have hsectorK (i : Fin 3) : (face i).carrier ⊆ K := by
    intro z hz
    obtain ⟨q, ⟨hq, ⟨p, hp, rfl⟩⟩, rfl⟩ := hsub (idx i) hz
    apply (hball hq.2).mpr
    fin_cases i <;> simp [idx, sectorParameterEquiv_apply, hp.1, hp.2]
  have hcoverK : W ∩ K ⊆ ⋃ i, (face i).carrier := by
    intro z hz
    have hzt : z ∈ J.target := hWt hz.1
    let q := J.symm z
    have hq : q ∈ J.source := J.map_target hzt
    have hqz : J q = z := J.right_inv hzt
    have hqside : q.1 ≤ 0 ∨ q.2 ≤ 0 := by
      apply (hball hq.2).mp
      change J q ∈ K
      rw [hqz]
      exact hz.2
    have hmember (i : Fin 3) (p : ℝ × ℝ) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2)
        (he : sectorParameterEquiv 0 (idx i) p = q) : z ∈ (face i).carrier := by
      apply hcover (idx i)
      refine ⟨hz.1, q, ⟨hq, p, hp, he⟩, hqz⟩
    by_cases hq1 : q.1 ≤ 0
    · by_cases hq2 : q.2 ≤ 0
      · exact mem_iUnion.mpr ⟨0, hmember 0 (-q.1, -q.2)
          ⟨neg_nonneg.mpr hq1, neg_nonneg.mpr hq2⟩ (by
            simp [idx, sectorParameterEquiv_apply])⟩
      · exact mem_iUnion.mpr ⟨1, hmember 1 (-q.1, q.2)
          ⟨neg_nonneg.mpr hq1, (lt_of_not_ge hq2).le⟩ (by
            simp [idx, sectorParameterEquiv_apply])⟩
    · have hq2 : q.2 ≤ 0 := hqside.resolve_left hq1
      exact mem_iUnion.mpr ⟨2, hmember 2 (q.1, -q.2)
        ⟨(lt_of_not_ge hq1).le, neg_nonneg.mpr hq2⟩ (by
          simp [idx, sectorParameterEquiv_apply])⟩
  refine ⟨r, face, W, hr, hrT, hsectorK, hW, hpW, hcoverK,
    hfirstEq (false, false) (false, true) rfl,
    hsecondEq (false, false) (true, false) rfl, ?_, ?_, ?_, ?_, ?_,
    fun i => hcoordinates (idx i)⟩
  · intro t ht
    simpa [face, idx, J, sectorParameterEquiv_apply] using hsecond (false, true) t ht
  · intro t ht
    simpa [face, idx, J, sectorParameterEquiv_apply] using hfirst (true, false) t ht
  · intro t
    simpa [face, idx, J, sectorParameterEquiv_apply] using hchord (false, false) t
  · intro t
    simpa [face, idx, J, sectorParameterEquiv_apply] using hchord (false, true) t
  · intro t
    simpa [face, idx, J, sectorParameterEquiv_apply] using hchord (true, false) t

end PoincareConjecture
