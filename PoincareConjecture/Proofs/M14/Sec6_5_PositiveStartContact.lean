import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartContactBounds
import PoincareConjecture.Proofs.M14.Sec6_5_VariationContact










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}




theorem exists_local_fixedTime_actionSet_bddBelow
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U) :
    ∃ N : Set G.Point, IsOpen N ∧ y ∈ N ∧
      ∀ q ∈ N, BddBelow (M14ActionSet G T a b x q) := by
  obtain ⟨N, hN, hyN, _, hfinite⟩ := exists_pastTube_finiteValueDomain hM12 p hp
  refine ⟨N ∩ U, hN.inter hU, ⟨hyN, hy⟩, ?_⟩
  intro q hq
  exact actionSet_bddBelow_of_pastFinite (p.tau_nonneg.trans_lt p.tau_lt)
    (hN.mem_nhds hq.1) ((hf q hq.2).contMDiffAt (hU.mem_nhds hq.2)).continuousAt hfinite





theorem isLocalMin_variationAction_gap_of_smooth_minimizing
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (V : M14LVariationData G p R)
    (hp : M14IsMinimizing p) (hfix : V.left_endpoint_fixed)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U) :
    IsLocalMin (fun v => M14VariationAction V v -
      (2 * Real.sqrt b) * M14ReducedLengthAt G T a x
        (V.squareFamily (Real.sqrt b) v)) 0 := by
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hc : 0 < 2 * Real.sqrt b := mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees (Real.sqrt b) hs, Real.sq_sqrt hb.le, p.curve_end]
  obtain ⟨N, hN, hyN, hbound⟩ := exists_local_fixedTime_actionSet_bddBelow hM12 hp U hU hy hf
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hη := ((variationEndpoint_contMDiffOn V hs).contMDiffAt
    (hP.mem_nhds hzero)).continuousAt
  have hnear : ∀ᶠ v in 𝓝 (0 : ℝ), V.squareFamily (Real.sqrt b) v ∈ N :=
    hη.preimage_mem_nhds (hN.mem_nhds (by rw [V.square_base, hpoint]; exact hyN))
  have hgap : M14VariationAction V 0 - (2 * Real.sqrt b) *
      M14ReducedLengthAt G T a x (V.squareFamily (Real.sqrt b) 0) = 0 := by
    rw [variationAction_zero V, V.square_base, hpoint, M14ReducedLengthAt,
      p.endpoint_time, sub_sub_cancel, reducedLengthValue_eq_of_minimizing p hp,
      mul_div_cancel₀ _ hc.ne', sub_self]
  filter_upwards [hP.mem_nhds hzero, hnear] with v hv hvN
  change M14VariationAction V 0 - (2 * Real.sqrt b) *
    M14ReducedLengthAt G T a x (V.squareFamily (Real.sqrt b) 0) ≤ _
  rw [hgap]
  obtain ⟨q, _⟩ := exists_initialFixed_variationEndpointPath hM12 V hfix hv
  have hfinite : M14FiniteValueDomain G T a b x (V.squareFamily (Real.sqrt b) v) :=
    ⟨⟨_, action_mem_actionSet q⟩, hbound _ hvN⟩
  have hle := reducedLengthAt_le_variationAction hM12 V hfix hv hfinite
  exact sub_nonneg.mpr (by simpa only [mul_comm] using (le_div_iff₀ hc).mp hle)

end PoincareConjecture.M14
