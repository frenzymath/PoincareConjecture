import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Critical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.NestedSlab

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem exists_localMin_in_open_sublevel
    {h : S2 → Real} (hh : Continuous h) {U : Set S2}
    (hU : IsOpen U) (hne : U.Nonempty) {c : Real}
    (hbelow : ∀ q ∈ U, h q < c) (hfront : ∀ q ∈ frontier U, h q = c) :
    ∃ q ∈ U, IsLocalMin h q := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq, hmin⟩ := isClosed_closure.isCompact.exists_isMinOn
    ⟨x, subset_closure hx⟩ hh.continuousOn
  have hlt : h q < c := (hmin (subset_closure hx)).trans_lt (hbelow x hx)
  have hqU : q ∈ U := by
    by_contra hout
    have hqf : q ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hq, hout⟩
    exact (ne_of_lt hlt) (hfront q hqf)
  exact ⟨q, hqU, hmin.isLocalMin
    (Filter.mem_of_superset (hU.mem_nhds hqU) subset_closure)⟩

private theorem exists_localExtremum_in_nested_cap (i : Fin 3) :
    ∃ q ∈ Saddle.Nested.capRegion i,
      IsLocalMin Saddle.Nested.height q ∨ IsLocalMax Saddle.Nested.height q := by
  open Saddle.Nested in
    have houter : outerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
      rw [lower_height_level_eq_sourceCircles]
      exact subset_union_left
    have hinner : innerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
      rw [lower_height_level_eq_sourceCircles]
      exact subset_union_right
    fin_cases i
    · obtain ⟨q, hq, hmin⟩ := exists_localMin_in_open_sublevel height_contMDiff.continuous
        isOpen_southernCap southernCap_nonempty (fun q hq => hq.1)
        (fun q hq => houter (frontier_southernCap_subset hq))
      exact ⟨q, hq, Or.inl hmin⟩
    · obtain ⟨q, hq, hmin⟩ := exists_localMin_in_open_sublevel height_contMDiff.continuous
        isOpen_northernCap northernCap_nonempty (fun q hq => hq.1)
        (fun q hq => hinner (frontier_northernCap_subset hq))
      exact ⟨q, hq, Or.inl hmin⟩
    · obtain ⟨q, hq, hmin⟩ := exists_localMin_in_open_sublevel height_contMDiff.continuous.neg
        isOpen_upperCap upperCap_nonempty (c := -(13 / 10))
        (fun q hq => neg_lt_neg (show 13 / 10 < height q from hq))
        (fun q hq => congrArg Neg.neg (show height q = 13 / 10 from frontier_upperCap_subset hq))
      refine ⟨q, hq, Or.inr ?_⟩
      simpa only [Pi.neg_apply, neg_neg] using hmin.neg

theorem nested_critical_outside_retainedBand_isLocalExtremum
    {q : S2} (hq : q ∉ Saddle.Nested.retainedBand)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height q = 0) :
    IsLocalMin Saddle.Nested.height q ∨ IsLocalMax Saddle.Nested.height q := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (Saddle.Nested.capRegion_cover.superset
    (show q ∈ Saddle.Nested.retainedBandᶜ from hq))
  obtain ⟨p, hp⟩ := Saddle.Nested.exists_unique_critical_in_each_cap
  obtain ⟨x, hx, hext⟩ := exists_localExtremum_in_nested_cap i
  have hxc : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height x = 0 := by
    rcases hext with hmin | hmax
    · exact Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin
        Saddle.Nested.height_contMDiff hmin
    · have hn := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin
        Saddle.Nested.height_contMDiff.neg hmax.neg
      change mfderiv (𝓡 2) 𝓘(Real, Real) (-Saddle.Nested.height) x = 0 at hn
      simpa only [mfderiv_neg, neg_eq_zero] using hn
  have hqx : q = x := ((hp i).2.2 q hi hc).trans ((hp i).2.2 x hx hxc).symm
  exact hqx ▸ hext

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_nested_model_chart_in_retainedBand
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.Nested.shear (3 / 10))
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    d.modelChart 0 ∈ Saddle.Nested.retainedBand := by
  have hc := terminal_model_chart_critical d hform
  have hnmin := terminal_model_chart_not_isLocalMin d hform
  have hnmax := terminal_model_chart_not_isLocalMax d hform
  rw [hmodel] at hc hnmin hnmax
  change mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height (d.modelChart 0) = 0 at hc
  change ¬ IsLocalMin Saddle.Nested.height (d.modelChart 0) at hnmin
  change ¬ IsLocalMax Saddle.Nested.height (d.modelChart 0) at hnmax
  by_contra hout
  exact (nested_critical_outside_retainedBand_isLocalExtremum hout hc).elim hnmin hnmax

theorem terminal_nested_model_chart_latitude
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.Nested.shear (3 / 10))
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    (d.modelChart 0 : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) := by
  have hc := terminal_model_chart_critical d hform
  rw [hmodel] at hc
  exact Saddle.Nested.critical_latitude_in_saddle_interval_of_height_band hc
    (terminal_nested_model_chart_in_retainedBand d hmodel hform)

theorem terminal_nested_model_chart_center
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.Nested.shear (3 / 10))
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {q : S2} (hc : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height q = 0)
    (hq : (q : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8)) : d.modelChart 0 = q := by
  have hdc := terminal_model_chart_critical d hform
  rw [hmodel] at hdc
  exact Saddle.Nested.critical_latitude_unique_in_saddle_interval hdc hc
    (Ioo_subset_Icc_self (terminal_nested_model_chart_latitude d hmodel hform))
    (Ioo_subset_Icc_self hq)

private def shiftHeight (c : Real) : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun y := y - c • (EuclideanSpace.single 2 1 : E3)
  invFun y := y + c • (EuclideanSpace.single 2 1 : E3)
  left_inv y := by simp
  right_inv y := by simp
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

theorem exists_terminal_nested_lower_slices_not_preconnected
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.Nested.shear (3 / 10))
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ico (-ε) (0 : Real),
      ¬ IsPreconnected (d.B (inner Real (M.v : E3) (g p) + t)) := by
  let c := inner Real (M.v : E3) (g p)
  let S := shiftHeight c
  let T := (d.transport.trans d.flatten).trans S
  have hc := terminal_model_chart_critical d hform
  rw [hmodel] at hc
  have hTheight (y : E3) : T y 2 =
      d.scale * (y 2 - Saddle.Nested.height (d.modelChart 0)) := by
    change (d.frame (d.D (d.transport y)) - c • (EuclideanSpace.single 2 1 : E3)) 2 = _
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul,
      mul_one]
    rw [d.frame_height, d.D_height, d.transport_height, hmodel]
    change c + d.scale * (y 2 - Saddle.Nested.height (d.modelChart 0)) - c = _
    ring
  obtain ⟨ε, hε, hcircles⟩ := Saddle.Nested.exists_uniform_negative_nested_level_circles
    T (Diffeomorph.refl (𝓡 3) E3 (n := ∞)) (fun _ => rfl) hc
    (terminal_nested_model_chart_latitude d hmodel hform) d.scale_pos hTheight
  refine ⟨ε, hε, ?_⟩
  intro t ht hpre
  obtain ⟨β, hβ, _, hdis, hcover, _⟩ := hcircles t ht
  have hS (x : E2) : S (Saddle.toE3 x (c + t)) = Saddle.toE3 x t := by
    change Saddle.toE3 x (c + t) - c • EuclideanSpace.single 2 1 = _
    ext i
    fin_cases i <;> simp [Saddle.toE3]
  have hslice : {x : E2 | Saddle.toE3 x t ∈
      (((Saddle.Nested.shear (3 / 10)).trans T).trans
        (Diffeomorph.refl (𝓡 3) E3 (n := ∞))) '' sphere (0 : E3) 1} = d.B (c + t) := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨d.transport (d.model y), ⟨y, hy, rfl⟩, ?_⟩
      apply S.injective
      change S (d.flatten (d.transport (d.model y))) = S (Saddle.toE3 x (c + t))
      rw [hS]
      rw [hmodel]
      exact heq
    · rintro ⟨_, ⟨y, hy, rfl⟩, heq⟩
      change d.flatten (d.transport (d.model y)) = Saddle.toE3 x (c + t) at heq
      refine ⟨y, hy, ?_⟩
      change S (d.flatten (d.transport (Saddle.Nested.shear (3 / 10) y))) = _
      rw [← hmodel, heq, hS]
  rw [hslice] at hcover
  have hcover' : range (β 0) ∪ range (β 1) = d.B (c + t) := by
    rw [← hcover]
    ext x
    simp only [mem_union, mem_iUnion, Fin.exists_fin_two]
  have hp : IsPreconnected (range (β 0) ∪ range (β 1)) := hcover'.symm ▸ hpre
  let q : sphere (0 : E2) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨x, _, hx0, hx1⟩ := isPreconnected_closed_iff.mp hp
    (range (β 0)) (range (β 1))
    (isCompact_range (hβ 0).contMDiff.continuous).isClosed
    (isCompact_range (hβ 1).contMDiff.continuous).isClosed subset_rfl
    ⟨β 0 q, Or.inl (mem_range_self q), mem_range_self q⟩
    ⟨β 1 q, Or.inr (mem_range_self q), mem_range_self q⟩
  exact disjoint_left.mp hdis hx0 hx1

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
