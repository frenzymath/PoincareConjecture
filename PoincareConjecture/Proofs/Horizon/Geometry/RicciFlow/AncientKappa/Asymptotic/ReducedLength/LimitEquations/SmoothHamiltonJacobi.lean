import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientHamiltonJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Slices
import Mathlib.MeasureTheory.Measure.OpenPos



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal
open Poincare.Analysis.Parabolic.WeakRegularity

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

local instance : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))).IsAddHaarMeasure
  infer_instance

theorem limitReducedLength_hamiltonJacobi_coordinates_of_smooth
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier)
    (hl : ContDiffOn ℝ ∞
      (fun z : Spacetime n => l ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1, z.2))
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).target ×ˢ Ioi (0 : ℝ)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let g := G.limit.flow.metric (-τ)
    let v := fun y => l (e y, τ)
    2 * deriv (fun s => l (e x, s)) τ +
      fderiv ℝ v x ((g.pullbackCoefficients e x).inverse (fderiv ℝ v x)) -
      (G.limit.flow.connection (-τ)).scalarCurvature (e x) + l (e x, τ) / τ = 0 := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let f := fun z : Spacetime n => l (e z.1, z.2)
  let D := e.source ×ˢ Ioi (0 : ℝ)
  let F := G.limit.flow
  let ρ := RicciFlow.BackwardCoordinates.density F e
  let A := RicciFlow.BackwardCoordinates.weightedPrincipal F e
  let B := fun z : Spacetime n => ρ z *
    (2 * Canonical.timeDeriv f z - (F.connection (-z.2)).scalarCurvature (e z.1) + f z / z.2) +
      ∑ i, ∑ j, A i j z * Canonical.spatialDeriv j f z * Canonical.spatialDeriv i f z
  have hD : IsOpen D := e.open_source.prod isOpen_Ioi
  have hdom : D = RicciFlow.BackwardCoordinates.domain (Iio 0) e :=
    (RicciFlow.BackwardCoordinates.domain_Iio_zero e).symm
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) D := hl.fderiv_of_isOpen hD (by simp)
  have hdt : ContDiffOn ℝ ∞ (Canonical.timeDeriv f) D := hdf.clm_apply contDiffOn_const
  have hdx (i : Fin n) : ContDiffOn ℝ ∞ (Canonical.spatialDeriv i f) D :=
    hdf.clm_apply contDiffOn_const
  have hρ : ContDiffOn ℝ ∞ ρ D := by
    rw [hdom]
    exact RicciFlow.BackwardCoordinates.contDiffOn_density F e
      contMDiffOn_chart_symm contMDiffOn_chart
  have hA (i j : Fin n) : ContDiffOn ℝ ∞ (A i j) D := by
    rw [hdom]
    exact RicciFlow.BackwardCoordinates.contDiffOn_weightedPrincipal F e
      contMDiffOn_chart_symm contMDiffOn_chart i j
  have hR : ContDiffOn ℝ ∞
      (fun z : Spacetime n => (F.connection (-z.2)).scalarCurvature (e z.1)) D := by
    rw [hdom]
    exact RicciFlow.BackwardCoordinates.contDiffOn_scalarCurvature_coordinates F e
      contMDiffOn_chart_symm contMDiffOn_chart
  have hB : ContinuousOn B D := by
    have hdt2 : ContDiffOn ℝ ∞ (fun z => 2 * Canonical.timeDeriv f z) D :=
      contDiffOn_const.mul hdt
    have hB' : ContDiffOn ℝ ∞ B D :=
      (hρ.mul ((hdt2.sub hR).add
        (hl.div contDiffOn_snd (fun z hz => ne_of_gt hz.2)))).add
        (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
          ((hA i j).mul (hdx j)).mul (hdx i))
    exact hB'.continuousOn
  have hformula (z : Spacetime n) (hz : z ∈ D) : B z = ρ z *
      (2 * deriv (fun s => l (e z.1, s)) z.2 +
        fderiv ℝ (fun y => l (e y, z.2)) z.1
          (((F.metric (-z.2)).pullbackCoefficients e z.1).inverse
            (fderiv ℝ (fun y => l (e y, z.2)) z.1)) -
        (F.connection (-z.2)).scalarCurvature (e z.1) + l (e z.1, z.2) / z.2) := by
    have hd : DifferentiableAt ℝ f z :=
      (hl.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
    have ht := (hd.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
    have hs (i : Fin n) :
        fderiv ℝ (fun y => f (y, z.2)) z.1 (EuclideanSpace.single i 1) =
          Canonical.spatialDeriv i f z :=
      RicciFlow.BackwardCoordinates.partialDeriv_spatialSlice hd i
    dsimp only [B]
    simp_rw [← hs]
    change ρ z * (2 * Canonical.timeDeriv f z - _ + f z / z.2) +
      (∑ i, ∑ j, LeviCivitaData.Dirichlet.divergenceCoefficients (F.metric (-z.2)) e z.1 i j *
        fderiv ℝ (fun y => f (y, z.2)) z.1 (EuclideanSpace.single j 1) *
        fderiv ℝ (fun y => f (y, z.2)) z.1 (EuclideanSpace.single i 1)) = _
    rw [LeviCivitaData.Dirichlet.sum_divergenceCoefficients_eq_inverse_pairing]
    change ρ z * (2 * Canonical.timeDeriv f z - _ + f z / z.2) + ρ z * _ = _
    change deriv (fun s => l (e z.1, s)) z.2 = Canonical.timeDeriv f z at ht
    rw [ht]
    dsimp only [f]
    ring
  obtain ⟨R, hRpos, hball⟩ := Metric.isOpen_iff.mp e.open_source x hx
  let r := R / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have hchart : Metric.closedBall x (2 * r) ⊆ e.source := by
    intro y hy
    apply hball
    have hd : dist y x ≤ 2 * r := hy
    change dist y x < R
    dsimp only [r] at hd
    linarith
  let U := Ioo (τ / 2) (τ + 1) ×ˢ Metric.ball x (r / 2)
  have hU : IsOpen U := isOpen_Ioo.prod Metric.isOpen_ball
  have hUD (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ U) : z.swap ∈ D := by
    refine ⟨hchart ((Metric.closedBall_subset_closedBall (by linarith))
      (Metric.ball_subset_closedBall hz.2)), ?_⟩
    exact (half_pos hτ).trans hz.1.1
  have ha := G.ae_limitReducedLength_hamiltonJacobi_coordinates
    P hσ l hlim q hr (half_pos hτ) (by linarith : τ / 2 ≤ τ + 1) hchart
  let ν : Measure (ℝ × EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hb : (fun z : ℝ × EuclideanSpace ℝ (Fin n) => B z.swap) =ᵐ[ν.restrict U] 0 := by
    have hmem : ∀ᵐ z ∂ν.restrict U, z ∈ U := ae_restrict_mem hU.measurableSet
    dsimp only [ν, U] at hmem ⊢
    rw [← Measure.prod_restrict] at hmem ⊢
    filter_upwards [ha, hmem] with z hz hzU
    change B z.swap = 0
    rw [hformula z.swap (hUD z hzU)]
    dsimp only [Prod.swap, e, F]
    rw [hz, mul_zero]
  have hBzero : EqOn (fun z : ℝ × EuclideanSpace ℝ (Fin n) => B z.swap) 0 U :=
    Measure.eqOn_open_of_ae_eq (μ := ν) hb hU
      (hB.comp continuous_swap.continuousOn hUD) continuousOn_const
  have hzU : (τ, x) ∈ U :=
    ⟨⟨half_lt_self hτ, by linarith⟩, Metric.mem_ball_self (half_pos hr)⟩
  have hz := hBzero hzU
  change B (x, τ) = 0 at hz
  rw [hformula (x, τ) ⟨hx, hτ⟩] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (RicciFlow.BackwardCoordinates.density_pos F e contMDiffOn_chart_symm contMDiffOn_chart
      (z := (x, τ)) hx).ne'

theorem limitReducedLength_hamiltonJacobi_of_smooth
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ)))
    (x : G.limit.carrier.carrier) {τ : ℝ} (hτ : 0 < τ) :
    let D := G.limit.flow.connection (-τ)
    let g := G.limit.flow.metric (-τ)
    let v := fun y => l (y, τ)
    2 * deriv (fun s => l (x, s)) τ +
      g.inner x (D.gradient v x) (D.gradient v x) - D.scalarCurvature x + l (x, τ) / τ = 0 := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
  let y := (chartAt (EuclideanSpace ℝ (Fin n)) x) x
  have hy : y ∈ e.source := (chartAt (EuclideanSpace ℝ (Fin n)) x).map_source (mem_chart_source _ x)
  have hey : e y = x := (chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv (mem_chart_source _ x)
  have hc : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : Spacetime n => l (e z.1, z.2)) (e.source ×ˢ Ioi (0 : ℝ)) :=
    hl.comp ((contMDiffOn_chart_symm.comp contMDiffOn_fst (fun z hz => hz.1)).prodMk
      contMDiffOn_snd) (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hc' : ContDiffOn ℝ ∞ (fun z : Spacetime n => l (e z.1, z.2))
      (e.source ×ˢ Ioi (0 : ℝ)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
    exact hc.contDiffOn
  have h := G.limitReducedLength_hamiltonJacobi_coordinates_of_smooth P hσ l hlim x hc' hy hτ
  have hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => l (z, τ)) :=
    contMDiffOn_univ.mp (hl.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun z _ => ⟨mem_univ z, hτ⟩))
  let g := G.limit.flow.metric (-τ)
  let D := G.limit.flow.connection (-τ)
  have hnorm := D.gradient_norm_sq_eq_inverse_pairing e contMDiffOn_chart_symm
    contMDiffOn_chart hy ((hv (e y)).mdifferentiableAt (by simp))
  change (g.tangentNorm (e y) (D.gradient (fun z => l (z, τ)) (e y))) ^ 2 = _ at hnorm
  have hn : 0 ≤ g.inner (e y) (D.gradient (fun z => l (z, τ)) (e y))
      (D.gradient (fun z => l (z, τ)) (e y)) := by
    by_cases hz : D.gradient (fun z => l (z, τ)) (e y) = 0
    · simp only [hz, map_zero, le_refl]
    · exact (g.pos _ _ hz).le
  rw [RiemannianMetric.tangentNorm, Real.sq_sqrt hn] at hnorm
  change g.inner (e y) (D.gradient (fun z => l (z, τ)) (e y))
      (D.gradient (fun z => l (z, τ)) (e y)) =
    fderiv ℝ (fun z => l (e z, τ)) y
      ((g.pullbackCoefficients e y).inverse (fderiv ℝ (fun z => l (e z, τ)) y)) at hnorm
  change 2 * deriv (fun s => l (e y, s)) τ +
    fderiv ℝ (fun z => l (e z, τ)) y
      ((g.pullbackCoefficients e y).inverse (fderiv ℝ (fun z => l (e z, τ)) y)) -
    D.scalarCurvature (e y) + l (e y, τ) / τ = 0 at h
  rw [← hnorm, hey] at h
  exact h

end PoincareConjecture.AncientCompactTimeConvergence
