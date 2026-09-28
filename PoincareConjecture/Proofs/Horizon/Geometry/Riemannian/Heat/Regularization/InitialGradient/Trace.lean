import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.Exhaustion








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)


theorem tendsto_initial_chart_derivative_of_exhaustion_integral
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfc : HasCompactSupport f)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hrep : ∀ t, 0 < t → ∀ x, F (t, x) = ∫ y,
      dirichletExhaustionKernel (fun j => heatKernelContinuousTime D (S j)) t x y * f y
        ∂g.volumeMeasure) (x : M) :
    Tendsto (fun p : ℝ × M => fderiv ℝ
      (fun z => F (p.1, (extChartAt (𝓡 n) x).symm z)) ((extChartAt (𝓡 n) x) p.2))
      (𝓝[Ioi 0 ×ˢ univ] (0, x))
      (𝓝 (fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm) ((extChartAt (𝓡 n) x) x))) := by
  let c := chartAt E x
  let z := c x
  have hx : x ∈ c.source := mem_chart_source E x
  have hz : z ∈ c.target := c.map_source hx
  obtain ⟨r, hr, hrc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (c.open_target.mem_nhds hz)
  have hVc : IsCompact (closure (Metric.ball z r)) :=
    (isCompact_closedBall z r).of_isClosed_subset isClosed_closure Metric.closure_ball_subset_closedBall
  have hKV : Metric.closedBall z (r / 2) ⊆ Metric.ball z r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  obtain ⟨C, hC, hbound⟩ := exists_exhaustion_integral_initial_fderiv_bound
    D hc hk hRic S hΩmono hcover c.symm contMDiffOn_chart_symm contMDiffOn_chart
    Metric.isOpen_ball hVc (Metric.closure_ball_subset_closedBall.trans hrc)
    (isCompact_closedBall z (r / 2)) hKV (convex_closedBall z (r / 2)) hf hfc
  let l : Filter (ℝ × M) := 𝓝[Ioi 0 ×ˢ (univ : Set M)] (0, x)
  have hccont : ContinuousAt c x := c.continuousOn.continuousAt (c.open_source.mem_nhds hx)
  have hspace : Tendsto (fun p : ℝ × M => c p.2) l (𝓝 z) :=
    (hccont.tendsto.comp continuousAt_snd.tendsto).mono_left nhdsWithin_le_nhds
  have htime : Tendsto (fun p : ℝ × M => p.1) l (𝓝 (0 : ℝ)) :=
    continuousAt_fst.tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ p : ℝ × M in l, 0 < p.1 ∧ c p.2 ∈ Metric.ball z (r / 2) := by
    filter_upwards [self_mem_nhdsWithin, hspace.eventually
      (Metric.ball_mem_nhds z (half_pos hr))] with p hp hpz
    exact ⟨hp.1, hpz⟩
  have hfcoord : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    contMDiffOn_iff_contDiffOn.mp
      ((hf.contMDiffOn (s := univ)).comp contMDiffOn_chart_symm (fun _ _ => mem_univ _))
  have hdf : Tendsto (fun p : ℝ × M => fderiv ℝ (f ∘ c.symm) (c p.2)) l
      (𝓝 (fderiv ℝ (f ∘ c.symm) z)) :=
    (((hfcoord.contDiffAt (c.open_target.mem_nhds hz)).fderiv_right
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).continuousAt.tendsto).comp hspace
  have herr : Tendsto (fun p : ℝ × M =>
      fderiv ℝ (fun w => F (p.1, c.symm w)) (c p.2) - fderiv ℝ (f ∘ c.symm) (c p.2))
      l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun p => C * p.1) _ (by simpa using htime.const_mul C)
    filter_upwards [hnear] with p hp
    have hpK : c p.2 ∈ interior (Metric.closedBall z (r / 2)) :=
      Metric.ball_subset_interior_closedBall hp.2
    have hpt : c p.2 ∈ c.target := hrc (Metric.ball_subset_closedBall (hKV
      (Metric.ball_subset_closedBall hp.2)))
    have hcsm : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (c p.2) :=
      contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hpt)
    have hFsm : ContDiffAt ℝ ∞ (fun w => F (p.1, c.symm w)) (c p.2) :=
      contMDiffAt_iff_contDiffAt.mp
        ((hF.contMDiffAt (x := (p.1, c.symm (c p.2)))
          ((isOpen_Ioi.prod isOpen_univ).mem_nhds
          ⟨hp.1, mem_univ _⟩)).comp (c p.2) (contMDiffAt_const.prodMk hcsm))
    have hfs := hfcoord.contDiffAt (c.open_target.mem_nhds hpt)
    have heq : (fun w => F (p.1, c.symm w) - f (c.symm w)) =
        (fun w => (∫ y, dirichletExhaustionKernel
          (fun j => heatKernelContinuousTime D (S j)) p.1 (c.symm w) y * f y
          ∂g.volumeMeasure) - f (c.symm w)) := by
      funext w
      rw [hrep p.1 hp.1]
    have hb := hbound p.1 hp.1 (c p.2) hpK
    rw [← heq] at hb
    rw [← fderiv_fun_sub (hFsm.differentiableAt (by simp))
      (hfs.differentiableAt (by simp))]
    simpa only [Function.comp_def] using hb
  have h := herr.add hdf
  simpa [sub_add_cancel, zero_add, extChartAt_coe, extChartAt_coe_symm,
    c, z, l, Function.comp_def] using h

end PoincareConjecture.LeviCivitaData.Dirichlet
