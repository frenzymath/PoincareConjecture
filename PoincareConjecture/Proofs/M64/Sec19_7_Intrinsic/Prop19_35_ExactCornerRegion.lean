import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCornerChart
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SignedCapContacts












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Triangles PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_exists_exact_loop_corner_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      (0 : ℝ × ℝ) ∈ H.source ∧ H 0 = gamma 0 ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      (∀ s : ℝ, H (s, 0) = gamma s) ∧
      (∀ s : ℝ, H (0, s) = gamma (T - s)) ∧
      (∀ q ∈ H.source, H q ∈ gamma '' Icc 0 T ↔
        (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)) ∧
      ((∀ q ∈ H.source, H q ∈ closure U ↔ 0 ≤ q.1 ∧ 0 ≤ q.2) ∨
        (∀ q ∈ H.source, H q ∈ closure U ↔ q.1 ≤ 0 ∨ q.2 ≤ 0)) := by
  obtain ⟨G, hG0, hbase, hG, hGi, haxis, haxis', hrays, _, _⟩ :=
    m64Intrinsic_exists_loop_corner_chart hg hT hend hinj hind
  let c := rightTriangleBasis (show (0 : ℝ) < 1 by norm_num)
  have hc0 : c 0 = (0 : AnnulusCoordinates) := by ext i; fin_cases i <;> rfl
  have hfront : G (c 0) ∈ frontier U := by
    rw [hc0, hbase, hfU]
    exact ⟨0, ⟨le_rfl, hT.le⟩, rfl⟩
  have hrays' : ∀ᶠ z in 𝓝 (c 0), G z ∈ frontier U ↔
      (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0) := by
    simpa [hc0, hfU, c, rightTriangleBasis_coord] using hrays
  have hside := m64Intrinsic_jordan_corner_germ hU hV hdisj (hfU.trans hfV.symm)
    G c (hc0 ▸ hG0) hfront hrays'
  let e := collarParameterEquiv.symm
  let J := e.toHomeomorph.toOpenPartialHomeomorph.trans G
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := by
    refine ⟨mem_univ _, ?_⟩
    change e 0 ∈ G.source
    simpa only [map_zero] using hG0
  have hJ : ContDiffOn ℝ ∞ J J.source :=
    (contMDiffOn_iff_contDiffOn.mp hG).comp e.contDiff.contDiffOn (fun _ hz => hz.2)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target :=
    e.symm.contDiff.comp_contDiffOn
      ((contMDiffOn_iff_contDiffOn.mp hGi).mono (fun _ hz => hz.1))
  have he : Tendsto e (𝓝 0) (𝓝 (0 : AnnulusCoordinates)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ℝ × ℝ)
  have hloop : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), J q ∈ gamma '' Icc 0 T ↔
      (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0) := by
    simpa [J, e, collarParameterEquiv] using he.eventually hrays
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
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hloop.and hside')
  let H := J.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  refine ⟨H, ⟨hJ0, mem_ball_self hR⟩, ?_, hJ.mono inter_subset_left,
    hJi.mono inter_subset_left, ?_, ?_, ?_, ?_⟩
  · change G (e 0) = gamma 0
    simpa only [map_zero] using hbase
  · intro s
    simpa [H, J, e, collarParameterEquiv] using haxis s
  · intro s
    simpa [H, J, e, collarParameterEquiv] using haxis' s
  · intro q hq
    exact (hball hq.2).1
  · cases positive
    · exact Or.inr (fun q hq => (hball hq.2).2)
    · exact Or.inl (fun q hq => (hball hq.2).2)

end PoincareConjecture
