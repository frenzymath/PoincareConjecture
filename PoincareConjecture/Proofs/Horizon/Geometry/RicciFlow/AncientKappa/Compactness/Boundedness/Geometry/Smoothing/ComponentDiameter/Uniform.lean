import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Charts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.AncientCompactness

local notation "I₃" => 𝓘(ℝ, CoordinateThree)

private theorem exists_centered_chart_ball
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateThree M]
    [IsManifold I₃ 1 M] {O : Set M} (hO : IsOpen O) {p : M} (hp : p ∈ O) :
    ∃ (e : OpenPartialHomeomorph M CoordinateThree) (r : ℝ),
      0 < r ∧ e.source ⊆ O ∧ p ∈ e.source ∧ e p = 0 ∧
      closedBall (0 : CoordinateThree) r ⊆ e.target ∧
      MDifferentiableOn I₃ I₃ e e.source ∧ MDifferentiableOn I₃ I₃ e.symm e.target := by
  let c := chartAt CoordinateThree p
  let q := c p
  let e := (c.restrOpen O hO).transHomeomorph (Homeomorph.addRight (-q))
  have heO : e.source ⊆ O := fun _ hx => hx.2
  have hpe : p ∈ e.source := ⟨mem_chart_source CoordinateThree p, hp⟩
  have hezero : e p = 0 := by change c p + -q = 0; exact add_neg_cancel q
  have hz : (0 : CoordinateThree) ∈ e.target := hezero ▸ e.map_source hpe
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target 0 hz
  refine ⟨e, r / 2, half_pos hr, heO, hpe, hezero, ?_, ?_, ?_⟩
  · exact fun x hx => hrsub ((closedBall_subset_ball (half_lt_self hr)) hx)
  · intro x hx
    have hc : MDifferentiableAt I₃ I₃ c x :=
      (contMDiffOn_chart (I := I₃) (n := 1) (x := p)).mdifferentiableOn one_ne_zero
        x hx.1 |>.mdifferentiableAt (c.open_source.mem_nhds hx.1)
    exact (hc.add mdifferentiableAt_const).mdifferentiableWithinAt
  · intro x hx
    have hxt : x - -q ∈ c.target := hx.1
    have hc : MDifferentiableAt I₃ I₃ c.symm (x - -q) :=
      (contMDiffOn_chart_symm (I := I₃) (n := 1) (x := p)).mdifferentiableOn one_ne_zero
        _ hxt |>.mdifferentiableAt (c.open_target.mem_nhds hxt)
    exact (hc.comp x (mdifferentiableAt_id.sub mdifferentiableAt_const)).mdifferentiableWithinAt

theorem exists_uniform_collared_regular_level_diameter
    {M : Type*} [MetricSpace M] [ChartedSpace CoordinateThree M]
    [IsManifold I₃ 1 M] {K O : Set M}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ d : ℝ, 0 < d ∧
      ∀ (f : M → ℝ), MDifferentiableOn I₃ 𝓘(ℝ, ℝ) f O →
        (∀ x ∈ O, mfderiv I₃ 𝓘(ℝ, ℝ) f x ≠ 0) →
      ∀ (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [ConnectedSpace Y],
      ∀ (U : Set M), IsOpen U → ∀ (s : ℝ) (hs : 0 < s),
      ∀ c : (Y × Ioo (-s) s) ≃ₜ U,
        (∀ y : Y, (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) ∈ K) →
      ∀ a : ℝ, (∀ y : Y, f (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)) = a) →
        ∃ y z : Y, d ≤ dist (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M)
          (c (z, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) := by
  classical
  have hcharts (p : K) := exists_centered_chart_ball hO (hKO p.property)
  choose e r hr heO hpe hezero hball he hei using hcharts
  let V : K → Set M := fun p => (e p).source ∩ (e p) ⁻¹' ball 0 (r p)
  have hV (p : K) : IsOpen (V p) :=
    (e p).continuousOn.isOpen_inter_preimage (e p).open_source isOpen_ball
  have hcover : K ⊆ ⋃ p : K, V p := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, hpe ⟨x, hx⟩, ?_⟩
    change (e ⟨x, hx⟩) x ∈ ball 0 (r ⟨x, hx⟩)
    rw [hezero]
    exact mem_ball_self (hr _)
  obtain ⟨d, hd, hlebesgue⟩ := lebesgue_number_lemma_of_metric hK hV hcover
  refine ⟨d, hd, ?_⟩
  intro f hf hreg Y _ _ _ U hU s hs c hcenter a hlevel
  by_contra! hsmall
  let y₀ : Y := Classical.choice inferInstance
  let x₀ : M := c (y₀, ⟨0, neg_lt_zero.mpr hs, hs⟩)
  obtain ⟨p, hp⟩ := hlebesgue x₀ (hcenter y₀)
  have hloc (y : Y) : (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) ∈ V p := by
    apply hp
    exact hsmall y y₀
  obtain ⟨x, hx, _, hcrit⟩ :=
    exists_critical_point_in_chart_ball_of_compact_connected_level_collar
      (e p) hU hs (hr p) c (fun y => (hloc y).1) (fun y => (hloc y).2)
      (hball p) (hf.mono (heO p)) (he p) (hei p) hlevel
  exact hreg x (heO p hx) hcrit

end PoincareConjecture.AncientCompactness
