import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCornerCoordinates
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SignedCapContacts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Triangles PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_exact_two_arc_corner_region
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {K U V O : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha 0 ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ K)
    (hfV : frontier V = frontier U) (hO : IsOpen O) (hpO : alpha 0 ∈ O) :
    ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      (0 : ℝ × ℝ) ∈ H.source ∧ H 0 = alpha 0 ∧ H.target ⊆ O ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      (∀ s : ℝ, H (s, 0) = alpha s) ∧ (∀ s : ℝ, H (0, s) = beta s) ∧
      (∀ q ∈ H.source, H q ∈ frontier U ↔
        (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)) ∧
      ((∀ q ∈ H.source, H q ∈ closure U ↔ 0 ≤ q.1 ∧ 0 ≤ q.2) ∨
        (∀ q ∈ H.source, H q ∈ closure U ↔ q.1 ≤ 0 ∨ q.2 ≤ 0)) := by
  obtain ⟨G, hG0, hGbase, hG, hGi, haxis, haxis', _, _⟩ :=
    m64Intrinsic_exists_two_arc_corner_chart isOpen_univ isOpen_univ
      (mem_univ 0) (mem_univ 0) ha.contDiffOn hb.contDiffOn hbase hind
  let c := rightTriangleBasis (show (0 : ℝ) < 1 by norm_num)
  have hc0 : c 0 = (0 : AnnulusCoordinates) := by ext i; fin_cases i <;> rfl
  have hline0 (s : ℝ) : AffineMap.lineMap (c 0) (c 1) s = !₂[s, 0] := by
    ext i
    fin_cases i <;> simp [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hline1 (s : ℝ) : AffineMap.lineMap (c 0) (c 2) s = !₂[0, s] := by
    ext i
    fin_cases i <;> simp [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hrays := m64Intrinsic_two_arc_frontier_germ G c (hc0 ▸ hG0) hA hB
    ha.continuous.continuousOn hb.continuous.continuousOn hai hbi
    (fun s => by rw [hline0]; exact haxis s)
    (fun s => by rw [hline1]; exact haxis' s) hK
    (by simpa only [hc0, hGbase] using hpK) hfU
  have hfront : G (c 0) ∈ frontier U := by
    rw [hc0, hGbase, hfU]
    exact Or.inl (Or.inl ⟨0, ⟨le_rfl, hA.le⟩, rfl⟩)
  have hside := m64Intrinsic_jordan_corner_germ hU hV hdisj hfV.symm
    G c (hc0 ▸ hG0) hfront hrays
  let e := collarParameterEquiv.symm
  let J := e.toHomeomorph.toOpenPartialHomeomorph.trans G
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := by
    refine ⟨mem_univ _, ?_⟩
    change e 0 ∈ G.source
    simpa only [map_zero] using hG0
  have hJbase : J 0 = alpha 0 := by
    change G (e 0) = alpha 0
    simpa only [map_zero] using hGbase
  have hJ : ContDiffOn ℝ ∞ J J.source :=
    (contMDiffOn_iff_contDiffOn.mp hG).comp e.contDiff.contDiffOn (fun _ hz => hz.2)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target :=
    e.symm.contDiff.comp_contDiffOn
      ((contMDiffOn_iff_contDiffOn.mp hGi).mono (fun _ hz => hz.1))
  have he : Tendsto e (𝓝 0) (𝓝 (0 : AnnulusCoordinates)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ℝ × ℝ)
  have hboundary : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), J q ∈ frontier U ↔
      (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0) := by
    have hrays' : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), G z ∈ frontier U ↔
        (z 0 = 0 ∧ 0 ≤ z 1) ∨ (0 ≤ z 0 ∧ z 1 = 0) := by
      simpa [hc0, c, rightTriangleBasis_coord] using hrays
    simpa [J, e, collarParameterEquiv] using he.eventually hrays'
  obtain ⟨positive, hside'⟩ : ∃ positive : Bool,
      ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), J q ∈ closure U ↔
        if positive then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0 := by
    rcases hside with hpos | hneg
    · refine ⟨true, ?_⟩
      have hpos' : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates),
          G z ∈ closure U ↔ 0 ≤ z 0 ∧ 0 ≤ z 1 := by
        simpa [hc0, c, rightTriangleBasis_coord] using hpos
      simpa [J, e, collarParameterEquiv] using he.eventually hpos'
    · refine ⟨false, ?_⟩
      have hneg' : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates),
          G z ∈ closure U ↔ z 0 ≤ 0 ∨ z 1 ≤ 0 := by
        simpa [hc0, c, rightTriangleBasis_coord] using hneg
      simpa [J, e, collarParameterEquiv] using he.eventually hneg'
  have hnear : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), J q ∈ O :=
    (J.continuousAt hJ0).eventually (hO.mem_nhds (hJbase.symm ▸ hpO))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hboundary.and (hside'.and hnear))
  let H := J.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  refine ⟨H, ⟨hJ0, mem_ball_self hR⟩, hJbase, ?_, hJ.mono inter_subset_left,
    hJi.mono inter_subset_left, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hs : H.symm z ∈ H.source := H.map_target hz
    have hmem : H (H.symm z) ∈ O := (hball hs.2).2.2
    rwa [H.right_inv hz] at hmem
  · intro s
    simpa [H, J, e, collarParameterEquiv] using haxis s
  · intro s
    simpa [H, J, e, collarParameterEquiv] using haxis' s
  · intro q hq
    exact (hball hq.2).1
  · cases positive
    · exact Or.inr (fun q hq => (hball hq.2).2.1)
    · exact Or.inl (fun q hq => (hball hq.2).2.1)

end PoincareConjecture
