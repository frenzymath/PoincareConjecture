import PoincareConjecture.Proofs.M14.Sec6_4_VariationGaugeAcceleration
import PoincareConjecture.Proofs.M14.Mathlib.RectanglePartialDerivative











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}



noncomputable def variationAccelerationField
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V) (s : ℝ) :
    G.Horizontal (R.curve s) := by
  classical
  exact if hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ then
    M14VariationEndpointAcceleration V D s hs else 0



theorem variationAccelerationField_eq
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    variationAccelerationField V D s = M14VariationEndpointAcceleration V D s hs := by
  simp only [variationAccelerationField, dif_pos hs]



noncomputable def variationAccelerationBoundaryPair
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V) (s : ℝ) : ℝ :=
  G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (variationAccelerationField V D s)

private theorem pair_transport_heq {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : HEq (h.symm ▸ v : G.Horizontal r) v := by
  cases h
  rfl

private theorem horizontal_inner_eq_of_heq {q r : G.Point} (h : q = r)
    {a z : G.Horizontal q} {a' z' : G.Horizontal r} (ha : HEq a a') (hz : HEq z z') :
    G.spacetime.horizontalMetric.inner q a z = G.spacetime.horizontalMetric.inner r a' z' := by
  cases h
  cases ha
  cases hz
  rfl



theorem variationAccelerationBoundaryPair_gauge
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (x₀ : G.gaugeCover.spatial b) {N P : Set ℝ}
    (hN : IsOpen N) (hP : IsOpen P) (hzero : (0 : ℝ) ∈ P) (hPsub : P ⊆ V.parameterDomain)
    {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
      ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P))
    (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
    (hclock : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
      (β (r, u)).1.val = T - r ^ 2)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N) :
    variationAccelerationBoundaryPair V D s =
      M08.chartActionMetric W.flow T x₀ (s, (β (s, 0)).2.val)
        (derivWithin (fun r => (β (r, 0)).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s)
        (deriv (deriv (fun v => (β (s, v)).2.val)) 0 +
          M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)
            (s, (β (s, 0)).2.val) (deriv (fun v => (β (s, v)).2.val) 0)
            (deriv (fun v => (β (s, v)).2.val) 0)) := by
  have hA₀ : HEq (R.horizontal_velocity s) (variationSquareVelocity V s 0) := by
    rw [variationSquareVelocity_zero V hs.1]
    exact (pair_transport_heq (V.square_base s).symm _).symm
  have hA := hA₀.trans (variationSquareVelocity_gauge V b hN hβ hrec hs hzero)
  have hZ := variationEndpointAcceleration_gauge V D b hCoordinates W x₀
    inter_subset_left hP hzero hPsub hβ hrec hclock hs
  unfold variationAccelerationBoundaryPair
  rw [variationAccelerationField_eq V D hs.1]
  exact (horizontal_inner_eq_of_heq
    ((hrec s hs 0 hzero).trans (V.square_base s)).symm hA hZ).trans
      (gauge_chartActionMetric b W T x₀ (β (s, 0)).2 s (β (s, 0)).1
        (hclock s hs 0 hzero).symm _ _).symm




theorem variationAccelerationBoundaryPair_contDiffOn
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals) :
    ContDiffOn ℝ ∞ (variationAccelerationBoundaryPair V D) (M14SqrtParameterInterval τ₁ τ₂) := by
  intro s hs
  obtain ⟨b, N, P, β, hN, hsN, hP, hzero, hPsub, hβ, hrec, hclock⟩ :=
    exists_variation_gauge_rectangle V hs
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  let S := M14SqrtParameterInterval τ₁ τ₂ ∩ N
  let x₀ := (β (s, 0)).2
  let q := fun z : ℝ × ℝ => (β z).2.val
  let a := fun r => derivWithin (fun v => q (v, 0)) S r
  let y := fun r => deriv (fun v => q (r, v)) 0
  let z := fun r => deriv (deriv (fun v => q (r, v))) 0 +
    M08.closedChartConnection W.flow T x₀ S (r, q (r, 0)) (y r) (y r)
  have hS : UniqueDiffOn ℝ S :=
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have hq : ContDiffOn ℝ ∞ q (S ×ˢ P) := variationGauge_spatial_contDiffOn b hβ
  have hmap : MapsTo (fun r : ℝ => (r, (0 : ℝ))) S (S ×ˢ P) := fun _ hr => ⟨hr, hzero⟩
  have hq₀ := hq.comp (contDiffOn_id.prodMk contDiffOn_const) hmap
  have hy₀ := hq.contDiffOn_deriv_snd_prod hS hP (k := ∞) (by simp)
  have hy : ContDiffOn ℝ ∞ y S := hy₀.comp (contDiffOn_id.prodMk contDiffOn_const) hmap
  have hyy : ContDiffOn ℝ ∞ (fun r => deriv (deriv (fun v => q (r, v))) 0) S :=
    (hy₀.contDiffOn_deriv_snd_prod hS hP (k := ∞) (by simp)).comp
      (contDiffOn_id.prodMk contDiffOn_const) hmap
  have ha : ContDiffOn ℝ ∞ a S :=
    (hq.contDiffOn_derivWithin_fst_prod hS hP.uniqueDiffOn (k := ∞) (by simp)).comp
      (contDiffOn_id.prodMk contDiffOn_const) hmap
  have htime (r : ℝ) (hr : r ∈ S) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr 0 hzero]
    exact (β (r, 0)).1.property
  have hpoint : ContDiffOn ℝ ∞ (fun r => (r, q (r, 0))) S := contDiffOn_id.prodMk hq₀
  have htarget : MapsTo (fun r => (r, q (r, 0))) S
      (S ×ˢ (extChartAt (𝓡 n) x₀).target) := by
    intro r hr
    refine ⟨hr, ?_⟩
    have hsrc : (β (r, 0)).2 ∈ (extChartAt (𝓡 n) x₀).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have heq : extChartAt (𝓡 n) x₀ (β (r, 0)).2 = q (r, 0) := by
      rw [extChartAt_coe]
      rfl
    change q (r, 0) ∈ (extChartAt (𝓡 n) x₀).target
    rw [← heq]
    exact (extChartAt (𝓡 n) x₀).map_source hsrc
  have hΓ := (M08.closedChartConnection_contDiffOn W.flow T x₀ hS htime).comp hpoint htarget
  have hz : ContDiffOn ℝ ∞ z S := hyy.add ((hΓ.clm_apply hy).clm_apply hy)
  have hmetric := (M08.chartActionMetric_closed_contDiffOn W.flow T x₀ htime).comp hpoint htarget
  have hpair := (hmetric.clm_apply ha).clm_apply hz
  have hactual : ContDiffOn ℝ ∞ (variationAccelerationBoundaryPair V D) S := by
    apply hpair.congr
    intro r hr
    exact variationAccelerationBoundaryPair_gauge V D b hCoordinates W x₀
      hN hP hzero hPsub hβ hrec hclock hr
  exact (contDiffWithinAt_inter (hN.mem_nhds hsN)).mp (hactual s ⟨hs, hsN⟩)




theorem secondVariationBoundaryTerm_eq_accelerationPair
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V) :
    M14SecondVariationBoundaryTerm V D =
      variationAccelerationBoundaryPair V D (Real.sqrt τ₂) -
        variationAccelerationBoundaryPair V D (Real.sqrt τ₁) := by
  have hleft : Real.sqrt τ₁ ∈ M14SqrtParameterInterval τ₁ τ₂ :=
    ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩
  have hright : Real.sqrt τ₂ ∈ M14SqrtParameterInterval τ₁ τ₂ :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  simp only [M14SecondVariationBoundaryTerm, variationAccelerationBoundaryPair,
    variationAccelerationField_eq V D hleft, variationAccelerationField_eq V D hright,
    M14SquareRootVelocity]

end PoincareConjecture.M14
