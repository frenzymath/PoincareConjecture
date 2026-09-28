import PoincareConjecture.Proofs.M14.Sec6_3_PrefixMinimality
import PoincareConjecture.Proofs.M14.Sec6_2_VariationPrefix
import PoincareConjecture.Proofs.M14.Sec6_2_VariationSlice









set_option autoImplicit false

open Set Filter
open scoped Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}




theorem isLocalMin_cornerVariationAction (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T a b x y) (hmin : M14IsMinimizing q)
    (p : M14BackwardPath G T a c x (q.curve c)) (hc : c < b)
    (haction : M14BackwardLAction G p =
      M14BackwardLAction G (prefixPath q c p.tau_lt hc.le))
    {Rp : M14SquareRootPath G p} {Rq : M14SquareRootPath G q}
    (Vp : M14LVariationData G p Rp) (Vq : M14LVariationData G q Rq)
    (hleft : Vp.left_endpoint_fixed) (hfix : M14BothEndpointsFixed Vq)
    (hjoin : ∀ u ∈ Vp.parameterDomain ∩ Vq.parameterDomain, Vp.family c u = Vq.family c u) :
    IsLocalMin (fun u => M14VariationAction Vp u + M14VariationAction Vq u -
      M14VariationAction (prefixVariation Vq p.tau_lt hc.le) u) 0 := by
  have hzero : (0 : ℝ) ∈ Vp.parameterDomain ∩ Vq.parameterDomain := by
    rw [Vp.parameterDomain_eq, Vq.parameterDomain_eq]
    exact ⟨⟨neg_lt_zero.mpr Vp.radius_pos, Vp.radius_pos⟩,
      ⟨neg_lt_zero.mpr Vq.radius_pos, Vq.radius_pos⟩⟩
  have hP : IsOpen (Vp.parameterDomain ∩ Vq.parameterDomain) := by
    rw [Vp.parameterDomain_eq, Vq.parameterDomain_eq]
    exact isOpen_Ioo.inter isOpen_Ioo
  have hcenter : M14VariationAction Vp 0 + M14VariationAction Vq 0 -
      M14VariationAction (prefixVariation Vq p.tau_lt hc.le) 0 = M14BackwardLAction G q := by
    rw [variationAction_zero, variationAction_zero, variationAction_zero, haction]
    ring
  change ∀ᶠ u in 𝓝 (0 : ℝ), _
  filter_upwards [hP.mem_nhds hzero] with u hu
  rw [hcenter]
  let qu := variationPath Vq hu.2
    (((Vq.left_endpoint_fixed_spec.mp hfix.1) u hu.2).trans q.curve_start)
    (((Vq.right_endpoint_fixed_spec.mp hfix.2) u hu.2).trans q.curve_end)
  let pu : M14BackwardPath G T a c x (qu.curve c) := variationPathBetween Vp hu.1
    (((Vp.left_endpoint_fixed_spec.mp hleft) u hu.1).trans p.curve_start) (hjoin u hu)
  have hcomp := minimizing_action_le_prefix_add_tail hM12 q hmin qu pu hc
  have hsplit : M14VariationAction (prefixVariation Vq p.tau_lt hc.le) u +
      (∫ s in c..b, M14BackwardLIntegrand G qu s) = M14VariationAction Vq u :=
    intervalIntegral.integral_add_adjacent_intervals
      (prefixPath qu c p.tau_lt hc.le).action_integrable
      (tailPath qu c p.tau_lt.le hc).action_integrable
  change M14BackwardLAction G q ≤ M14VariationAction Vp u +
    (∫ s in c..b, M14BackwardLIntegrand G qu s) at hcomp
  linarith

end PoincareConjecture.M14
