import PoincareConjecture.Proofs.M14.Sec6_3_GaugeEndpointFamily
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVectorVariation

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem GaugeEndpointFamily.diagonal_eventually_mem
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : ℝ × P → G.Point} {U : Set P} {T a b c : ℝ} {p₀ : P}
    {j : G.gaugeCover.index}
    {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j}
    (D : GaugeEndpointFamily f U T a b c p₀ j lift) :
    ∀ᶠ r in 𝓝 p₀, (r, (lift (f (c, r))).2.val) ∈ D.parameters :=
  (continuousAt_id.prodMk D.coordinate_smooth.continuousAt).preimage_mem_nhds
    (D.parameters_open.mem_nhds D.center_mem)

theorem exists_exponentialLine_endpointFamily
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x)
    {b c : ℝ} (hb : (Z, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {V : Set G.Point} (hV : IsOpen V)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift V)
    (hright : ∀ q ∈ V, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hcenter : E.gamma Z c ∈ V) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      (∀ r ∈ U, (Z + r • W, b) ∈ E.domain) ∧
      Nonempty (GaugeEndpointFamily (fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1)
        U T 0 b c 0 j lift) := by
  have hbpos : 0 < b := hc.1.trans hc.2
  obtain ⟨A, hsurvive, hA⟩ := exists_initialVectorVariation hM04 hM12 E Z W hb hbpos
  have hU : IsOpen A.parameterDomain := A.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ A.parameterDomain := by
    rw [A.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr A.radius_pos, A.radius_pos⟩
  have hC : M14SqrtParameterInterval 0 (b ^ 2) = Icc 0 b := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hbpos.le]
  have hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1) (Icc 0 b ×ˢ A.parameterDomain) := by
    have h := A.square_smooth.mono A.square_contains
    rw [hC] at h
    exact h.congr (fun z hz => (hA z.1 (hC.symm ▸ hz.1) z.2).symm)
  have hclock (s : ℝ) (hs : s ∈ Icc 0 b) (r : ℝ) (hr : r ∈ A.parameterDomain) :
      G.spacetime.timeFunction (E.gamma (Z + r • W) s) = T - s ^ 2 :=
    E.clock _ _ ((E.maximal_lifetime _).out (E.domain_zero _) (hsurvive r hr) hs)
  refine ⟨A.parameterDomain, hU, hzero, hsurvive, ?_⟩
  exact gaugeEndpointFamily_nonempty _ hU hzero hc hf hclock j lift hV hlift hright
    (by simpa only [zero_smul, add_zero] using hcenter)

end PoincareConjecture.M14
