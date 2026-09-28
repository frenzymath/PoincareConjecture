import PoincareConjecture.Proofs.M14.Sec6_4_VariationSurfaceBridge
import PoincareConjecture.Proofs.M14.Sec6_4_VariationGaugeDerivative
import PoincareConjecture.Proofs.M14.Sec6_4_BaseGaugeFields
import PoincareConjecture.Proofs.M14.Sec6_4_SurfaceGaugeCoefficients










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
  (D : M14VariationDerivativeData V) (b : G.gaugeCover.index)
  (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
  (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
    (horizontalScalarCurvature G.leafwise))
  (hM04 : RicciFlowCurvatureTheory.{0})
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
  (x₀ : G.gaugeCover.spatial b) {N P : Set ℝ} (hN : IsOpen N) (hP : IsOpen P)
  (hzero : (0 : ℝ) ∈ P)
  {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b}
  (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
    ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P))
  (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
    (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
  (hclock : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
    (β (r, u)).1.val = T - r ^ 2)

private theorem horizontal_function_eq_of_heq
    (f : ∀ q : G.Point, G.Horizontal q → G.Horizontal q → G.Horizontal q → ℝ)
    {q r : G.Point} (h : q = r)
    {a v d : G.Horizontal q} {a' v' d' : G.Horizontal r}
    (ha : HEq a a') (hv : HEq v v') (hd : HEq d d') : f q a v d = f r a' v' d' := by
  cases h
  cases ha
  cases hv
  cases hd
  rfl

include hCoordinates hscalar hM04 hN hP hzero hβ hrec hclock




theorem surfaceIndex_gauge {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hsN : s ∈ N) :
    let q := fun z : ℝ × ℝ => (β z).2.val
    let m := M08.chartActionMetric W.flow T x₀
    let Γ := M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)
    let a := M08.coordinatePartialS q (s, 0)
    let v := M08.coordinatePartialU q (s, 0)
    let d := M08.coordinateCovariantS Γ q (M08.coordinatePartialU q) (s, 0)
    let P₀ := fun z => M08.chartActionPotential W.flow T x₀ (s, z)
    m (s, q (s, 0)) d d +
        m (s, q (s, 0)) (M08.coordinateCurvature Γ (s, q (s, 0)) v a v) a -
        m (s, q (s, 0)) (fderiv ℝ Γ (s, q (s, 0)) (1, 0) v v) a +
        (fderiv ℝ (fderiv ℝ P₀) (q (s, 0)) v v -
          fderiv ℝ P₀ (q (s, 0)) (Γ (s, q (s, 0)) v v)) =
      M14SecondVariationIndexDensity V D s := by
  let S := M14SqrtParameterInterval τ₁ τ₂ ∩ N
  let Ω := (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∩ N) ×ˢ P
  let q := fun z : ℝ × ℝ => (β z).2.val
  let Γ := M08.closedChartConnection W.flow T x₀ S
  let j : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (β (s, 0))) :=
    (G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
  have hsS : s ∈ S := ⟨Ioo_subset_Icc_self hs, hsN⟩
  have hSneigh : S ∈ 𝓝 s := inter_mem (Icc_mem_nhds hs.1 hs.2) (hN.mem_nhds hsN)
  have hS : UniqueDiffOn ℝ S :=
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have htime (r : ℝ) (hr : r ∈ S) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr 0 hzero]
    exact (β (r, 0)).1.property
  have hΩ : IsOpen Ω := (isOpen_Ioo.inter hN).prod hP
  have hq : ContDiffOn ℝ ∞ q Ω := (variationGauge_spatial_contDiffOn b hβ).mono
    (fun _ hz => ⟨⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩, hz.2⟩)
  have hp : (s, (0 : ℝ)) ∈ Ω := ⟨⟨hs, hsN⟩, hzero⟩
  have hqd := (hq.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hβ₀ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun r => β (r, 0)) S :=
    hβ.comp (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ)))).contMDiffOn
      (fun _ hr => ⟨hr, hzero⟩)
  have hbase (r : ℝ) (hr : r ∈ S) :
      (G.gaugeCover.cylinder b).toSpacetime (β (r, 0)) = R.curve r :=
    (hrec r hr 0 hzero).trans (V.square_base r)
  have hAcoord : derivWithin (fun r => q (r, 0)) S s = M08.coordinatePartialS q (s, 0) := by
    rw [derivWithin_of_mem_nhds hSneigh]
    exact (M08.coordinateSlice_fst_hasDerivAt q hqd).deriv
  have hYcoord : deriv (fun v => q (s, v)) 0 = M08.coordinatePartialU q (s, 0) :=
    (M08.coordinateSlice_snd_hasDerivAt q hqd).deriv
  have hDYcoord := coordinateCovariantS_partialU_eq_slice hΩ q hq hp Γ hSneigh
  have hA := (squareRootVelocity_gauge R b hN hβ₀ hbase hsS).trans
    (heq_of_eq (congrArg (fun v : EuclideanSpace ℝ (Fin n) => j v) hAcoord))
  have hY := (variationField_gauge V b hP hzero hβ hrec hsS).trans
    (heq_of_eq (congrArg (fun v : EuclideanSpace ℝ (Fin n) => j v) hYcoord))
  have hDY := (variationCovariantDerivative_gauge V D b hCoordinates W x₀
    hN hP hzero hβ hrec hclock hsS).trans
      (heq_of_eq (congrArg (fun v : EuclideanSpace ℝ (Fin n) => j v) hDYcoord.symm))
  have htransport := horizontal_function_eq_of_heq (G := G)
    (fun q a v d => G.spacetime.horizontalMetric.inner q d d +
      horizontalRiemann G.leafwise q v a a v +
      2 * s ^ 2 * M14HorizontalHessianPairing G q v v -
      4 * s * M14HorizontalRicciDerivativePairing G q v a v +
      2 * s * M14HorizontalRicciDerivativePairing G q a v v)
    (hbase s hsS).symm hA hY hDY
  exact (gauge_surfaceIndex_expression b W hCoordinates hscalar hM04 T hS htime x₀
    (β (s, 0)).2 hsS hSneigh (β (s, 0)).1 (hclock s hsS 0 hzero).symm _ _ _).trans
      htransport.symm




theorem surfaceEuler_gauge (hPsub : P ⊆ V.parameterDomain) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hsN : s ∈ N) :
    let q := fun z : ℝ × ℝ => (β z).2.val
    let m := M08.chartActionMetric W.flow T x₀
    let Γ := M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)
    let a := M08.coordinatePartialS q (s, 0)
    let z := M08.coordinateCovariantU Γ q (M08.coordinatePartialU q) (s, 0)
    let d := M08.coordinateCovariantS Γ q (M08.coordinatePartialS q) (s, 0)
    let P₀ := fun z => M08.chartActionPotential W.flow T x₀ (s, z)
    m (s, q (s, 0)) d z - fderiv ℝ P₀ (q (s, 0)) z +
        fderiv ℝ m (s, q (s, 0)) (1, 0) a z =
      M14SquareRootEulerResidual G R D.base_extension s (variationAccelerationField V D s) := by
  let S := M14SqrtParameterInterval τ₁ τ₂ ∩ N
  let Ω := (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∩ N) ×ˢ P
  let q := fun z : ℝ × ℝ => (β z).2.val
  let Γ := M08.closedChartConnection W.flow T x₀ S
  let j : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (β (s, 0))) :=
    (G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
  have hsS : s ∈ S := ⟨Ioo_subset_Icc_self hs, hsN⟩
  have hSneigh : S ∈ 𝓝 s := inter_mem (Icc_mem_nhds hs.1 hs.2) (hN.mem_nhds hsN)
  have hS : UniqueDiffOn ℝ S :=
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have htime (r : ℝ) (hr : r ∈ S) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr 0 hzero]
    exact (β (r, 0)).1.property
  have hΩ : IsOpen Ω := (isOpen_Ioo.inter hN).prod hP
  have hq : ContDiffOn ℝ ∞ q Ω := (variationGauge_spatial_contDiffOn b hβ).mono
    (fun _ hz => ⟨⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩, hz.2⟩)
  have hp : (s, (0 : ℝ)) ∈ Ω := ⟨⟨hs, hsN⟩, hzero⟩
  have hqd := (hq.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
  have hβ₀ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun r => β (r, 0)) S :=
    hβ.comp (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ)))).contMDiffOn
      (fun _ hr => ⟨hr, hzero⟩)
  have hbase (r : ℝ) (hr : r ∈ S) :
      (G.gaugeCover.cylinder b).toSpacetime (β (r, 0)) = R.curve r :=
    (hrec r hr 0 hzero).trans (V.square_base r)
  have hAcoord : derivWithin (fun r => q (r, 0)) S s = M08.coordinatePartialS q (s, 0) := by
    rw [derivWithin_of_mem_nhds hSneigh]
    exact (M08.coordinateSlice_fst_hasDerivAt q hqd).deriv
  have hDAcoord := coordinateCovariantS_partialS_eq_slice hΩ q hq hp Γ hSneigh
  have hZcoord := coordinateCovariantU_partialU_eq_slice hΩ q hq hp Γ
  have hA := (squareRootVelocity_gauge R b hN hβ₀ hbase hsS).trans
    (heq_of_eq (congrArg (fun v : EuclideanSpace ℝ (Fin n) => j v) hAcoord))
  have hDA := (squareRootCovariantVelocity_gauge R b hCoordinates W x₀ hN hβ₀ hbase
    (fun r hr => hclock r hr 0 hzero) D.base_extension hsS).trans
      (heq_of_eq (congrArg (fun v : EuclideanSpace ℝ (Fin n) => j v) hDAcoord.symm))
  have hZ : HEq (variationAccelerationField V D s)
      (j (M08.coordinateCovariantU Γ q (M08.coordinatePartialU q) (s, 0))) := by
    rw [variationAccelerationField_eq V D hsS.1]
    exact (variationEndpointAcceleration_gauge V D b hCoordinates W x₀
      inter_subset_left hP hzero hPsub hβ hrec hclock hsS).trans
        (heq_of_eq (congrArg (fun v : EuclideanSpace ℝ (Fin n) => j v) hZcoord.symm))
  have htransport := horizontal_function_eq_of_heq (G := G)
    (fun q a d z => G.spacetime.horizontalMetric.inner q d z -
      2 * s ^ 2 * M14HorizontalScalarDifferential G q z.val +
      4 * s * horizontalRicci G.leafwise q a z)
    (hbase s hsS).symm hA hDA hZ
  exact (gauge_surfaceEuler_expression b W hCoordinates hscalar hM04 T hS htime x₀
    (β (s, 0)).2 hsS hSneigh (β (s, 0)).1 (hclock s hsS 0 hzero).symm _ _ _).trans
      htransport.symm

end PoincareConjecture.M14
