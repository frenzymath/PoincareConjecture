import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Source

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_potential_oscillation_bound (S : GradientShrinkingSolitonData 3 M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p x : M,
      |S.potential x - S.potential p| ≤
        (S.potentialGradientScale p + C * (S.metric.edist p x).toReal) *
          (S.metric.edist p x).toReal := by
  obtain ⟨C, hC, hbound⟩ := S.exists_hessian_quadratic_bound
  refine ⟨C, hC, fun p x => ?_⟩
  by_cases hpx : p = x
  · subst x
    let := S.metric.toMetricSpace
    have heq : S.metric.edist p p = 0 := by change edist p p = 0; exact edist_self p
    simp [heq]
  have hL : 0 < (S.metric.edist p x).toReal := by
    let := S.metric.toMetricSpace
    change 0 < dist p x
    exact dist_pos.mpr hpx
  let L := (S.metric.edist p x).toReal
  obtain ⟨γ, hγ0, hγL, hgeo, hspeed, _⟩ :=
    S.metric.exists_unit_speed_minimizing_geodesic_of_metricComplete S.complete p x hL
  change γ L = x at hγL
  let v := fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1
  let f := S.potential ∘ γ
  let d := deriv f
  have hf (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ 1 f s :=
    contMDiffAt_iff_contDiffAt.mp (((S.potential_contMDiff _).of_le (by simp)).comp s
      (hgeo.contMDiffAt hs))
  have hd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt d
      (S.connection.hessian S.potential (γ s) (v s) (v s)) s :=
    S.connection.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn isOpen_univ
      S.potential_contMDiff.contMDiffOn hgeo hs (mem_univ _)
  have hunit (s : ℝ) (hs : s ∈ Icc 0 L) :
      S.metric.inner (γ s) (v s) (v s) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨S.metric.toRiemannianMetric⟩
    have hn : 0 ≤ S.metric.inner (γ s) (v s) (v s) := by
      change 0 ≤ inner ℝ (v s) (v s)
      exact real_inner_self_nonneg
    have hsquare := Real.sq_sqrt hn
    change (S.metric.tangentNorm (γ s) (v s)) ^ 2 = _ at hsquare
    rw [hspeed s hs] at hsquare
    norm_num at hsquare
    exact hsquare.symm
  have hdosc (s : ℝ) (hs : s ∈ Icc 0 L) : |d s - d 0| ≤ C * L := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun r hr => (hd r hr).hasDerivWithinAt)
      (fun r hr => by
        rw [Real.norm_eq_abs]
        simpa only [hunit r (Ico_subset_Icc_self hr), mul_one] using hbound (γ r) (v r))
      s hs
    simpa only [Real.norm_eq_abs, sub_zero] using
      h.trans (mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using hs.2) hC)
  have hd0 : |d 0| ≤ S.potentialGradientScale p := by
    have hγd := (hgeo.contMDiffAt (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)).mdifferentiableAt
      (by simp : (1 : ℕ∞ω) ≠ 0)
    have hder : HasDerivAt f (mvfderiv (𝓡 3) S.potential (γ 0) (v 0)) 0 :=
      (((S.potential_contMDiff _).mdifferentiableAt (by simp)).hasMFDerivAt.comp 0
        hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
    have h := S.connection.abs_mvfderiv_le_gradient_norm S.potential (γ 0) (v 0)
    rw [hspeed 0 ⟨le_rfl, hL.le⟩, mul_one, ← hder.deriv, hγ0] at h
    exact h
  have hdabs (s : ℝ) (hs : s ∈ Icc 0 L) :
      |d s| ≤ S.potentialGradientScale p + C * L := by
    have htri : |d s| ≤ |d s - d 0| + |d 0| := by
      simpa only [sub_add_cancel] using abs_add_le (d s - d 0) (d 0)
    linarith [hdosc s hs]
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun r hr => ((hf r hr).differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt)
    (fun r hr => by simpa only [Real.norm_eq_abs] using hdabs r (Ico_subset_Icc_self hr))
    L (show L ∈ Icc 0 L from ⟨hL.le, le_rfl⟩)
  simpa only [Real.norm_eq_abs, sub_zero, f, Function.comp_apply, hγ0, hγL] using h

theorem exists_normalizedPotential_ball_bound (S : GradientShrinkingSolitonData 3 M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : M, 1 ≤ S.potentialGradientScale p →
      ∀ r : ℝ, 0 ≤ r → ∀ x : M, (S.metric.edist p x).toReal ≤ r →
        |S.normalizedPotential p x| ≤ r + C * r ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := S.exists_potential_oscillation_bound
  refine ⟨C, hC, fun p hp r hr x hx => ?_⟩
  let d := (S.metric.edist p x).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have ha : 0 < S.potentialGradientScale p := lt_of_lt_of_le zero_lt_one hp
  rw [normalizedPotential, abs_div, abs_of_pos ha]
  apply (div_le_iff₀ ha).mpr
  have h := hbound p x
  change |S.potential x - S.potential p| ≤ (S.potentialGradientScale p + C * d) * d at h
  have hdr : d ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hd hx 2
  have hCdr := mul_le_mul_of_nonneg_left hdr hC
  have hadr := mul_le_mul_of_nonneg_left hx ha.le
  have hmul := mul_le_mul_of_nonneg_left hp (mul_nonneg hC (sq_nonneg r))
  nlinarith

theorem normalizedPotential_eventually_bounded_on_balls
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x : M,
      (S.metric.edist (q k) x).toReal ≤ r → |S.normalizedPotential (q k) x| ≤ B := by
  obtain ⟨C, hC, hbound⟩ := S.exists_normalizedPotential_ball_bound
  refine ⟨r + C * r ^ 2, by positivity, ?_⟩
  have ha := S.potentialGradientScale_tendsto_atTop_of_escape hD p q hescape
  filter_upwards [ha.eventually_ge_atTop 1] with k hk
  exact hbound (q k) hk r hr

end PoincareConjecture.GradientShrinkingSolitonData
