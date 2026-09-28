import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


theorem exists_cap_chart_side_buffer
    (A : BallNeighborhoodChart E3 E3)
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (R : ℝ) (hR : 1 < R)
    (hzero : ∀ X : E2, ‖X‖ < R → (X, (0 : ℝ)) ∈ C.source)
    (hcentral : ∀ X : E2, ‖X‖ < R →
      C (X, 0) = A.chart (referenceCapPoint a X))
    (X0 : E2) (hX0 : ‖X0‖ ≤ 1)
    (d b0 : ℝ) (hd : 0 < d) (hb0 : 0 < b0)
    (hanchor_neg : ∀ s : ℝ, -d < s → s < 0 → C (X0, s) ∈ A.inside)
    (hanchor_pos : ∀ s : ℝ, 0 < s → s < d → C (X0, s) ∈ A.closedRegionᶜ) :
    ∃ ε b : ℝ, 0 < ε ∧ 1 + ε < R ∧ 0 < b ∧ b < b0 ∧ b < d ∧
      closedBall (0 : E2) (1 + ε) ×ˢ Icc (-b) b ⊆ C.source ∧
      (∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ, |s| ≤ b →
        (C (X, s) ∈ A.boundary ↔ s = 0)) ∧
      (∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ,
        -b < s → s < 0 → C (X, s) ∈ A.inside) ∧
      ∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ,
        0 < s → s < b → C (X, s) ∈ A.closedRegionᶜ := by
  let P := referenceCapSphereChart a ha
  obtain ⟨hPs, _, hP, _, _, _, _⟩ := referenceCapSphereChart_spec a ha
  let j : UnitTwoSphere → E3 := fun q => A.chart (q : E3)
  have hj : Continuous j := by
    apply continuousOn_univ.mp
    exact A.chart.continuousOn.comp continuous_subtype_val.continuousOn
      (fun q _ => A.closedBall_subset_source (sphere_subset_closedBall q.2))
  have hji : Function.Injective j := by
    intro q q' heq
    apply Subtype.ext
    exact A.chart.injOn
      (A.closedBall_subset_source (sphere_subset_closedBall q.2))
      (A.closedBall_subset_source (sphere_subset_closedBall q'.2)) heq
  let O : Set UnitTwoSphere := P '' ball (0 : E2) R
  have hO : IsOpen O := P.isOpen_image_of_subset_source isOpen_ball
    (fun X _ => hPs.symm ▸ mem_univ X)
  let L : Set E3 := j '' Oᶜ
  have hL : IsCompact L := hO.isClosed_compl.isCompact.image hj
  have hcentral' (X : E2) (hX : ‖X‖ < R) : C (X, 0) = j (P X) := by
    change C (X, 0) = A.chart (P X : E3)
    rw [hP X]
    exact hcentral X hX
  have hnotL (X : E2) (hX : ‖X‖ < R) : j (P X) ∉ L := by
    rintro ⟨q, hq, heq⟩
    have hqeq := hji heq
    apply hq
    rw [hqeq]
    exact ⟨X, mem_ball_zero_iff.mpr hX, rfl⟩
  let ε : ℝ := (R - 1) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hrR : 1 + ε < R := by dsimp only [ε]; linarith
  let W : Set (E2 × ℝ) := C.source ∩ C ⁻¹' Lᶜ
  have hW : IsOpen W := C.isOpen_inter_preimage hL.isClosed.isOpen_compl
  have hWzero : closedBall (0 : E2) (1 + ε) ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨X, s⟩ ⟨hX, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have hXR : ‖X‖ < R := (mem_closedBall_zero_iff.mp hX).trans_lt hrR
    refine ⟨hzero X hXR, ?_⟩
    change C (X, 0) ∉ L
    rw [hcentral' X hXR]
    exact hnotL X hXR
  obtain ⟨V1, V2, _, hV2, hKV1, h0V2, hVV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : E2) (1 + ε))
      (isCompact_singleton (x := (0 : ℝ))) hW hWzero
  obtain ⟨w, hw, hwV2⟩ := Metric.mem_nhds_iff.mp
    (hV2.mem_nhds (h0V2 (mem_singleton 0)))
  let b := min w (min b0 d) / 2
  have hmin : 0 < min w (min b0 d) := lt_min hw (lt_min hb0 hd)
  have hb : 0 < b := div_pos hmin (by norm_num)
  have hbw : b < w := by
    dsimp only [b]
    linarith only [min_le_left w (min b0 d), hmin]
  have hbb0 : b < b0 := by
    dsimp only [b]
    linarith only [min_le_right w (min b0 d), min_le_left b0 d, hmin]
  have hbd : b < d := by
    dsimp only [b]
    linarith only [min_le_right w (min b0 d), min_le_right b0 d, hmin]
  have hcylinder : closedBall (0 : E2) (1 + ε) ×ˢ Icc (-b) b ⊆ W := by
    intro p hp
    apply hVV
    refine ⟨hKV1 hp.1, hwV2 ?_⟩
    apply mem_ball_zero_iff.mpr
    simpa only [Real.norm_eq_abs] using (abs_le.mpr hp.2).trans_lt hbw
  have hboundary (X : E2) (hX : ‖X‖ ≤ 1 + ε) (s : ℝ) (hs : |s| ≤ b) :
      C (X, s) ∈ A.boundary ↔ s = 0 := by
    have hXball : X ∈ closedBall (0 : E2) (1 + ε) := mem_closedBall_zero_iff.mpr hX
    have hWpoint : (X, s) ∈ W := hcylinder ⟨hXball, abs_le.mp hs⟩
    constructor
    · rintro ⟨y, hy, heq⟩
      let q : UnitTwoSphere := ⟨y, hy⟩
      have hqO : q ∈ O := by
        by_contra hq
        exact hWpoint.2 ⟨q, hq, heq⟩
      obtain ⟨X', hX', hPX'⟩ := hqO
      have hX'R := mem_ball_zero_iff.mp hX'
      have heq' : C (X', 0) = C (X, s) :=
        (hcentral' X' hX'R).trans ((congrArg j hPX').trans heq)
      have hp := C.injOn hWpoint.1 (hzero X' hX'R) heq'.symm
      exact congrArg Prod.snd hp
    · intro hs0
      subst s
      rw [hcentral X (hX.trans_lt hrR)]
      exact ⟨referenceCapPoint a X, referenceCapPoint_mem_sphere a ha X, rfl⟩
  let N : Set E3 := C '' (closedBall (0 : E2) (1 + ε) ×ˢ Ioo (-b) 0)
  let Pside : Set E3 := C '' (closedBall (0 : E2) (1 + ε) ×ˢ Ioo 0 b)
  have hNsource : closedBall (0 : E2) (1 + ε) ×ˢ Ioo (-b) 0 ⊆ C.source := by
    intro p hp
    exact (hcylinder ⟨hp.1, hp.2.1.le, hp.2.2.le.trans hb.le⟩).1
  have hPsource : closedBall (0 : E2) (1 + ε) ×ˢ Ioo 0 b ⊆ C.source := by
    intro p hp
    exact (hcylinder ⟨hp.1, (neg_nonpos.mpr hb.le).trans hp.2.1.le, hp.2.2.le⟩).1
  have hN : IsPreconnected N :=
    ((convex_closedBall (0 : E2) (1 + ε)).isPreconnected.prod isPreconnected_Ioo).image
      C (C.continuousOn.mono hNsource)
  have hPside : IsPreconnected Pside :=
    ((convex_closedBall (0 : E2) (1 + ε)).isPreconnected.prod isPreconnected_Ioo).image
      C (C.continuousOn.mono hPsource)
  have hcover (y : E3) (hy : y ∉ A.boundary) : y ∈ A.inside ∪ A.closedRegionᶜ := by
    by_cases hin : y ∈ A.inside
    · exact Or.inl hin
    · right
      intro hclosed
      rw [← A.inside_union_boundary] at hclosed
      exact hclosed.elim hin hy
  have hNcover : N ⊆ A.inside ∪ A.closedRegionᶜ := by
    rintro _ ⟨⟨X, s⟩, ⟨hX, hs⟩, rfl⟩
    apply hcover
    intro hbdry
    have hsabs : |s| ≤ b := abs_le.mpr ⟨hs.1.le, hs.2.le.trans hb.le⟩
    exact hs.2.ne ((hboundary X (mem_closedBall_zero_iff.mp hX) s hsabs).mp hbdry)
  have hPcover : Pside ⊆ A.inside ∪ A.closedRegionᶜ := by
    rintro _ ⟨⟨X, s⟩, ⟨hX, hs⟩, rfl⟩
    apply hcover
    intro hbdry
    have hsabs : |s| ≤ b :=
      abs_le.mpr ⟨(neg_nonpos.mpr hb.le).trans hs.1.le, hs.2.le⟩
    exact hs.1.ne' ((hboundary X (mem_closedBall_zero_iff.mp hX) s hsabs).mp hbdry)
  have hIO : Disjoint A.inside A.closedRegionᶜ := disjoint_left.mpr fun _ hi ho =>
    ho (image_mono ball_subset_closedBall hi)
  have hNside := hN.subset_or_subset A.inside_open
    A.closedRegion_compact.isClosed.isOpen_compl hIO hNcover
  have hPside' := hPside.subset_or_subset A.inside_open
    A.closedRegion_compact.isClosed.isOpen_compl hIO hPcover
  have hX0ball : X0 ∈ closedBall (0 : E2) (1 + ε) :=
    mem_closedBall_zero_iff.mpr (hX0.trans (by linarith))
  have hNanchor : C (X0, -b / 2) ∈ N :=
    ⟨(X0, -b / 2), ⟨hX0ball, by constructor <;> linarith⟩, rfl⟩
  have hPanchor : C (X0, b / 2) ∈ Pside :=
    ⟨(X0, b / 2), ⟨hX0ball, by constructor <;> linarith⟩, rfl⟩
  have hNi : C (X0, -b / 2) ∈ A.inside :=
    hanchor_neg _ (by linarith) (by linarith)
  have hPo : C (X0, b / 2) ∈ A.closedRegionᶜ :=
    hanchor_pos _ (by linarith) (by linarith)
  have hNinside : N ⊆ A.inside := hNside.resolve_right fun hNo =>
    disjoint_left.mp hIO hNi (hNo hNanchor)
  have hPoutside : Pside ⊆ A.closedRegionᶜ := hPside'.resolve_left fun hPi =>
    disjoint_left.mp hIO (hPi hPanchor) hPo
  refine ⟨ε, b, hε, hrR, hb, hbb0, hbd, fun p hp => (hcylinder hp).1,
    hboundary, ?_, ?_⟩
  · intro X hX s hs hs0
    exact hNinside ⟨(X, s), ⟨mem_closedBall_zero_iff.mpr hX, hs, hs0⟩, rfl⟩
  · intro X hX s hs0 hs
    exact hPoutside ⟨(X, s), ⟨mem_closedBall_zero_iff.mpr hX, hs0, hs⟩, rfl⟩

end PoincareConjecture.M25.Topology3D
