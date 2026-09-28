import PoincareConjecture.Proofs.M14.Sec6_3_InitialJacobi
import PoincareConjecture.Proofs.M14.Sec6_3_InitialGaugeNeighborhood
import PoincareConjecture.Proofs.M14.Sec6_3_InitialGaugeVelocity











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}

private theorem horizontal_t2Space {p : G.Point} : T2Space (G.Horizontal p) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal p

attribute [local instance] horizontal_t2Space




theorem initialValuePath_differential_initialDerivative
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) (W : G.Horizontal x) :
    ∃ h : P.square_path.curve 0 = x,
      h ▸ M14JacobiFirstDerivative (initialValuePath_differentialData hM04 hM12 P W) 0 =
        (2 : ℝ) • W := by
  obtain ⟨b, ⟨t₀, x₀⟩, rfl⟩ := G.gaugeCover.covers x
  let base := (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal base) :=
    (metric.toCore base).toNormedAddCommGroupOfTopology
      (metric.continuousAt base) (metric.isVonNBounded base)
  let : InnerProductSpace ℝ (G.Horizontal base) :=
    .ofCoreOfTopology (metric.toCore base) (metric.continuousAt base) (metric.isVonNBounded base)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let Q := initialValuePath_differentialData hM04 hM12 P W
  let S := Real.sqrt τ
  have hS : 0 < S := Real.sqrt_pos.mpr P.path.tau_lt
  have hC : M14SqrtParameterInterval 0 τ = Icc 0 S := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, S]
  have hbase : G.spacetime.timeFunction base = T := by
    simpa only [GeneralizedFlowSpacetime.timeFunction, sub_zero] using P.path.base_time
  have hsurv : (Z, S) ∈ initialValueDomain G T base := by
    refine Or.inr ⟨hS, y, ?_⟩
    rw [show S ^ 2 = τ from Real.sq_sqrt P.path.tau_lt.le]
    exact ⟨P⟩
  obtain ⟨U, hU, hZU, htube, hsm⟩ :=
    initialValueCurve_smooth_prefix hM04 hM12 hbase hS hsurv
  obtain ⟨N, hN, hZN, hNU, d, hd, hdS, β, hβ, hrec, hclock, hzero⟩ :=
    exists_smooth_initial_gaugeFamily b t₀ x₀ hU hZU hS
      (fun z : G.Horizontal base × ℝ => initialValueCurve G T base z.1 z.2) hsm
      (fun A _ => initialValueCurve_zero A)
  have hsub : Icc 0 d ⊆ Icc 0 S := Icc_subset_Icc le_rfl hdS
  have hsubP : Icc 0 d ⊆ M14SqrtParameterInterval 0 τ := by rwa [hC]
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hβslice (A : G.Horizontal base) (hA : A ∈ N) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun t => β (A, t)) (Icc 0 d) :=
    hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ ht => ⟨hA, ht⟩)
  have hrecP (t : ℝ) (ht : t ∈ Icc 0 d) :
      (G.gaugeCover.cylinder b).toSpacetime (β (Z, t)) = P.square_path.curve t :=
    (hrec (Z, t) ⟨hZN, ht⟩).trans (initialValueCurve_eqOn_square hM04 hM12 P (hsubP ht))
  have hcl (t : ℝ) (ht : t ∈ Icc 0 d) : (β (Z, t)).1.val = T - t ^ 2 :=
    (hclock (Z, t) ⟨hZN, ht⟩).trans
      (initialValueCurve_clock hbase (htube ⟨hNU hZN, hsub ht⟩))
  let f : ℝ × G.Horizontal base → EuclideanSpace ℝ (Fin n) := fun z => (β (z.2, z.1)).2.val
  have hf : ContDiffOn ℝ ∞ f (Icc 0 d ×ˢ N) := by
    have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
        (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
      contMDiff_subtype_val
    have hq := hval.comp_contMDiffOn (fun z hz => (hβ z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hq
    exact hq.contDiffOn.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hz => ⟨hz.2, hz.1⟩)
  let Y : ℝ → EuclideanSpace ℝ (Fin n) := fun t => fderiv ℝ (fun A => f (t, A)) Z W
  let j := (G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀
  let L : G.Horizontal base →L[ℝ] EuclideanSpace ℝ (Fin n) := j.symm.toContinuousLinearMap
  have hv : (fun A => derivWithin (fun t => f (t, A)) (Icc 0 d) 0) =ᶠ[𝓝 Z]
      (fun A => (2 : ℝ) • L A) := by
    filter_upwards [hN.mem_nhds hZN] with A hA
    exact initialValueCurve_gauge_initialVelocity hM04 hM12 b t₀ x₀ hS hd hdS
      (htube ⟨hNU hA, hS.le, le_rfl⟩) (hβslice A hA)
      (fun t ht => hrec (A, t) ⟨hA, ht⟩) (hzero A hA)
  have hlin : HasFDerivAt (fun A => (2 : ℝ) • L A) ((2 : ℝ) • L) Z :=
    L.hasFDerivAt.const_smul (2 : ℝ)
  have hYd : derivWithin Y (Icc 0 d) 0 = (2 : ℝ) • L W := by
    have h := (hasDerivWithinAt_parameterDerivative_Icc hd hN f hf h0 hZN W).derivWithin
      (uniqueDiffOn_Icc hd 0 h0)
    rw [hv.fderiv_eq, hlin.fderiv] at h
    exact h
  have hY0 : Y 0 = 0 := by
    have heq : (fun A => f (0, A)) =ᶠ[𝓝 Z] (fun _ => x₀.val) := by
      filter_upwards [hN.mem_nhds hZN] with A hA
      exact congrArg (fun z => z.2.val) (hzero A hA)
    change fderiv ℝ (fun A => f (0, A)) Z W = 0
    rw [heq.fderiv_eq, fderiv_const_apply]
    rfl
  have hfield (t : ℝ) (ht : t ∈ Icc 0 d) : HEq (Q.field t)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β (Z, t)).1 (β (Z, t)).2 (Y t)) := by
    have hp : ContMDiffOn (𝓘(ℝ, G.Horizontal base)) (spacetimeModel n) ∞
        (fun A => β (A, t)) N :=
      hβ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hA => ⟨hA, ht⟩)
    have hg : (fun A => initialValueCurve G T base A t) =ᶠ[𝓝 Z]
        (fun A => (G.gaugeCover.cylinder b).toSpacetime (β (A, t))) := by
      filter_upwards [hN.mem_nhds hZN] with A hA
      exact (hrec (A, t) ⟨hA, ht⟩).symm
    have hdiff := gaugeMap_projectedDifferential_congr b
      ((hp.contMDiffAt (hN.mem_nhds hZN)).mdifferentiableAt (by simp)) hg W
    exact (initialValuePath_differentialField_heq hM04 hM12 P W (hsubP ht)).trans hdiff
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  let F := Classical.choice (ordinaryGaugeWitness_nonempty b hCoordinates)
  have hR := P.square_path.smooth.mono P.square_path.interval_subset
  have hres := horizontalCovariantDerivative_restrict_subset Q.extension hsubP
    (uniqueDiffOn_Icc hd 0 h0) ((hR 0 (hsubP h0)).mdifferentiableWithinAt (by simp))
  have hfirst := (heq_of_eq hres).trans
    (horizontalCovariantDerivative_lifted_gauge b hCoordinates F T x₀ (hβslice Z hZN)
      hrecP hcl (pullbackExtensionRestrict Q.extension hsubP) Y hfield h0
      (uniqueDiffOn_Icc hd 0 h0))
  rw [hzero Z hZN, hY0, map_zero, add_zero, hYd] at hfirst
  change HEq (M14JacobiFirstDerivative Q 0) (j ((2 : ℝ) • j.symm W)) at hfirst
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply] at hfirst
  let hstart := P.initial_velocity.choose
  exact ⟨hstart, eq_of_heq ((eqRec_heq hstart (M14JacobiFirstDerivative Q 0)).trans hfirst)⟩

end PoincareConjecture.M14
