import PoincareConjecture.Proofs.M14.Sec6_4_AccelerationPair
import PoincareConjecture.Proofs.M14.Sec6_4_SurfacePartials
import PoincareConjecture.Proofs.M08.SecondVariationBoundary

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} (V : M14LVariationData G p R)
  (b : G.gaugeCover.index)
  (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
  (x₀ : G.gaugeCover.spatial b) {N P : Set ℝ} (hN : IsOpen N) (hP : IsOpen P)
  {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b}
  (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
    ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P))
  (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
    (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
  (hclock : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
    (β (r, u)).1.val = T - r ^ 2)

private theorem surface_inner_eq_of_heq {q r : G.Point} (h : q = r)
    {a z : G.Horizontal q} {a' z' : G.Horizontal r} (ha : HEq a a') (hz : HEq z z') :
    G.spacetime.horizontalMetric.inner q a z = G.spacetime.horizontalMetric.inner r a' z' := by
  cases h
  cases ha
  cases hz
  rfl

include hCoordinates hN hP hβ hrec hclock

theorem surfaceActionDensity_gauge {s u : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hsN : s ∈ N) (hu : u ∈ P) :
    M08.surfaceActionDensity (M08.chartActionMetric W.flow T x₀)
      (M08.chartActionPotential W.flow T x₀) (fun z => (β z).2.val) (s, u) =
      variationActionDensity V (s, u) := by
  have hsC : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N := ⟨Ioo_subset_Icc_self hs, hsN⟩
  have hSneigh : M14SqrtParameterInterval τ₁ τ₂ ∩ N ∈ 𝓝 s :=
    inter_mem (Icc_mem_nhds hs.1 hs.2) (hN.mem_nhds hsN)
  have hq := variationGauge_spatial_contDiffOn b hβ
  have hqd := (hq.contDiffAt (prod_mem_nhds hSneigh (hP.mem_nhds hu))).differentiableAt
    (by simp)
  have hA : M08.coordinatePartialS (fun z => (β z).2.val) (s, u) =
      derivWithin (fun r => (β (r, u)).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s := by
    rw [derivWithin_of_mem_nhds hSneigh]
    exact (M08.coordinateSlice_fst_hasDerivAt _ hqd).deriv.symm
  have hv := variationSquareVelocity_gauge V b hN hβ hrec hsC hu
  have hm := surface_inner_eq_of_heq (hrec s hsC u hu) hv.symm hv.symm
  unfold M08.surfaceActionDensity
  dsimp only [Prod.fst, Prod.snd]
  rw [hA, gauge_chartActionMetric b W T x₀ (β (s, u)).2 s (β (s, u)).1
    (hclock s hsC u hu).symm,
    gauge_chartActionPotential b W hCoordinates T x₀ (β (s, u)).2 s (β (s, u)).1
      (hclock s hsC u hu).symm, hm, hrec s hsC u hu]
  unfold variationActionDensity
  ring

theorem surfaceAccelerationBoundaryPair_gauge (D : M14VariationDerivativeData V)
    (hzero : (0 : ℝ) ∈ P) (hPsub : P ⊆ V.parameterDomain)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hsN : s ∈ N) :
    M08.surfaceAccelerationBoundaryPair (M08.chartActionMetric W.flow T x₀)
      (M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N))
      (fun z => (β z).2.val) (s, 0) = variationAccelerationBoundaryPair V D s := by
  let Ω := (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∩ N) ×ˢ P
  let q := fun z : ℝ × ℝ => (β z).2.val
  have hΩ : IsOpen Ω := (isOpen_Ioo.inter hN).prod hP
  have hq : ContDiffOn ℝ ∞ q Ω := (variationGauge_spatial_contDiffOn b hβ).mono
    (fun _ hz => ⟨⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩, hz.2⟩)
  have hp : (s, (0 : ℝ)) ∈ Ω := ⟨⟨hs, hsN⟩, hzero⟩
  have hqd := (hq.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hSneigh : M14SqrtParameterInterval τ₁ τ₂ ∩ N ∈ 𝓝 s :=
    inter_mem (Icc_mem_nhds hs.1 hs.2) (hN.mem_nhds hsN)
  have hA : M08.coordinatePartialS q (s, 0) =
      derivWithin (fun r => q (r, 0)) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s := by
    rw [derivWithin_of_mem_nhds hSneigh]
    exact (M08.coordinateSlice_fst_hasDerivAt q hqd).deriv.symm
  have hZ := coordinateCovariantU_partialU_eq_slice hΩ q hq hp
    (M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N))
  change M08.chartActionMetric W.flow T x₀ (s, q (s, 0))
    (M08.coordinatePartialS q (s, 0))
    (M08.coordinateCovariantU
      (M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)) q
      (M08.coordinatePartialU q) (s, 0)) = _
  rw [hA, hZ]
  exact (variationAccelerationBoundaryPair_gauge V D b hCoordinates W x₀ hN hP hzero hPsub
    hβ hrec hclock ⟨Ioo_subset_Icc_self hs, hsN⟩).symm

end PoincareConjecture.M14
