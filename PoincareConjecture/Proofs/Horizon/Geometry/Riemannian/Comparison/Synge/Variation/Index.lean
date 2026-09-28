import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.Variation.Realization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.PieceDeriv
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.MinimalVariation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.Synge

open CoordinateExponential ConnectionVariation ConnectionAlongCurve ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {γ η₀ η₁ : ℝ → M}
  {V : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}

theorem GeodesicVariation.source (R : GeodesicVariation g γ V a b η₀ η₁)
    {i : ℕ} (hi : i < R.N) {t : ℝ} (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
    γ t ∈ (extChartAt (𝓡 n) (R.β i)).source :=
  R.base_source i hi t ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩

theorem GeodesicVariation.time_subset (R : GeodesicVariation g γ V a b η₀ η₁)
    {i : ℕ} (hi : i < R.N) : Icc (R.τ i) (R.τ (i + 1)) ⊆ Icc a b := by
  intro t ht
  exact ⟨(R.time_mem i (by omega)).1.trans ht.1,
    ht.2.trans (R.time_mem (i + 1) (by omega)).2⟩

theorem GeodesicVariation.sum_index_nonneg [T2Space M]
    (R : GeodesicVariation g γ V a b η₀ η₁) (D : LeviCivitaData g)
    {I : Set ℝ} (hsub : Icc a b ⊆ I) (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    {C : ℝ} (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc a b, g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C)
    (hmin : ∀ᶠ s in 𝓝 (0 : ℝ),
      ENNReal.ofReal ((b - a) * C) ≤ g.edist (η₀ s) (η₁ s)) :
    0 ≤ ∑ i ∈ Finset.range R.N, ∫ t in (R.τ i)..(R.τ (i + 1)),
      intrinsicIndexIntegrand g D γ V t := by
  classical
  let B := fun i => g.pullbackCoefficients (extChartAt (𝓡 n) (R.β i)).symm
  let A := fun i => christoffelBilinear (B i)
  let E := fun i s => ∫ t in (R.τ i)..(R.τ (i + 1)), energyDensity (B i) (R.u i) (0, 1) (s, t)
  have hτ (i : ℕ) (_hi : i < R.N) : R.τ i ≤ R.τ (i + 1) := (R.strict i).le
  have hG (i : ℕ) : ContDiffOn ℝ 2 (B i) (extChartAt (𝓡 n) (R.β i)).target :=
    (g.contDiffOn_chartCoefficients (R.β i)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hA (i : ℕ) : ContDiffOn ℝ 1 (A i) (extChartAt (𝓡 n) (R.β i)).target := by
    intro x hx
    have hAx : ContDiffAt ℝ ∞ (A i) x := contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients (R.β i)).contDiffAt
        ((isOpen_extChartAt_target (R.β i)).mem_nhds hx))
      (g.isInvertible_chartCoefficients (R.β i) hx)
    exact (hAx.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).contDiffWithinAt
  have htube (i : ℕ) (hi : i < R.N) :
      ∀ p ∈ Ioo (-R.ε) R.ε ×ˢ Ioo (R.τ i - R.ε) (R.τ (i + 1) + R.ε),
        R.u i p ∈ (extChartAt (𝓡 n) (R.β i)).target := by
    intro p hp
    exact R.tube i hi p ⟨hp.1,
      ⟨by linarith [hp.2.1, R.ε_le_ρ], by linarith [hp.2.2, R.ε_le_ρ]⟩⟩
  have hzero (i : ℕ) (hi : i < R.N) (t : ℝ) (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
      energyDensity (B i) (R.u i) (0, 1) (0, t) = (1 / 2 : ℝ) * C ^ 2 := by
    rw [energyDensity_eq_half_tangentNorm_sq g (R.β i)
      ((hgeo.contMDiffAt (hsub (R.time_subset hi ht))).mdifferentiableAt one_ne_zero)
      (R.source hi ht) ((R.smooth i hi).differentiable (by norm_num) _) (R.base i hi t ht),
      hspeed t (R.time_subset hi ht)]
  have hjunction : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i < R.N,
      (extChartAt (𝓡 n) (R.β i)).symm (R.u i (s, R.τ i)) = R.η i s ∧
      (extChartAt (𝓡 n) (R.β i)).symm (R.u i (s, R.τ (i + 1))) = R.η (i + 1) s := by
    have hfinite : ∀ i ∈ Finset.range R.N, ∀ᶠ s in 𝓝 (0 : ℝ),
        (extChartAt (𝓡 n) (R.β i)).symm (R.u i (s, R.τ i)) = R.η i s ∧
        (extChartAt (𝓡 n) (R.β i)).symm (R.u i (s, R.τ (i + 1))) = R.η (i + 1) s := by
      intro i hi
      filter_upwards [R.junction_left i (Finset.mem_range.mp hi),
        R.junction_right i (Finset.mem_range.mp hi)] with s hs hs'
      exact ⟨hs.1 ▸ (extChartAt (𝓡 n) (R.β i)).left_inv hs.2,
        hs'.1 ▸ (extChartAt (𝓡 n) (R.β i)).left_inv hs'.2⟩
    simpa only [Finset.mem_range] using (eventually_all_finset (Finset.range R.N)).mpr hfinite
  obtain ⟨l, r, hlr, hwindow⟩ := (hjunction.and hmin).exists_Ioo_subset
  let ε := min R.ε (min (-l) r)
  have hε : 0 < ε := lt_min R.ε_pos (lt_min (neg_pos.mpr hlr.1) hlr.2)
  have hεR : ε ≤ R.ε := min_le_left _ _
  have hεl : ε ≤ -l := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall {s : ℝ} (hs : s ∈ Ioo (-ε) ε) : s ∈ Ioo (-R.ε) R.ε :=
    ⟨by linarith [hs.1], hs.2.trans_le hεR⟩
  have hj {s : ℝ} (hs : s ∈ Ioo (-ε) ε) := hwindow
    (show s ∈ Ioo l r from ⟨by linarith [hs.1], hs.2.trans_le hεr⟩)
  have hlocal : IsLocalMin (fun s => ∑ i ∈ Finset.range R.N, E i s) 0 :=
    Poincare.VolumeComparison.Conjugate.isLocalMin_sum_chartEnergy_of_endpoint_distance_lower_bound
      g R.τ R.β R.u R.η hε hC hτ R.smooth
      (fun s hs i hi t ht => R.tube i hi (s, t)
        ⟨hsmall hs, ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩⟩)
      (fun _ hs i hi => ((hj hs).1 i hi).1)
      (fun _ hs i hi => ((hj hs).1 i hi).2)
      (fun s hs => by simpa only [R.endpoint_left, R.endpoint_right, R.left, R.right]
        using (hj hs).2) hzero
  have hfirst (i : ℕ) (hi : i < R.N) (s : ℝ) (hs : s ∈ Ioo (-R.ε) R.ε) :
      HasDerivAt (E i) (deriv (E i) s) s := by
    exact (hasDerivAt_pieceEnergy (hτ i hi) R.ε_pos (hG i) (R.smooth i hi)
      (htube i hi) hs).differentiableAt.hasDerivAt
  have hsecond (i : ℕ) (hi : i < R.N) :
      HasDerivAt (deriv (E i))
        (∫ t in (R.τ i)..(R.τ (i + 1)), chartIndexIntegrand (B i) (A i) (R.u i) t) 0 := by
    apply hasDerivAt_deriv_pieceEnergy_chartIndexIntegrand (hτ i hi) R.ε_pos
      (isOpen_extChartAt_target (R.β i)) (fun _ _ _ => g.symm _ _ _)
      (christoffelBilinear_chart_symm g (R.β i))
      (fun _ hx => isMetricCompatibleAt_chartCoefficients g (R.β i) hx)
      (hG i) (hA i) (R.smooth i hi) (htube i hi)
    · intro t ht
      exact covDerivAlong_fderiv_eq_zero_of_geodesic g (R.β i) hgeo
        (hsub (R.time_subset hi ht)) (R.source hi ht)
        (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
        (fun s => (hasDerivAt_const s (0 : ℝ)).prodMk (hasDerivAt_id s))
        (R.base i hi t ht)
    · exact covDerivAlong_fderiv_eq_zero_of_geodesic g (R.β i) (R.junction_geodesic i)
        ⟨by linarith [R.δ_pos i], R.δ_pos i⟩ (R.junction_left i hi).self_of_nhds.2
        (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
        (fun s => (hasDerivAt_id s).prodMk (hasDerivAt_const s (R.τ i)))
        ((R.junction_left i hi).mono fun _ h => h.1)
    · exact covDerivAlong_fderiv_eq_zero_of_geodesic g (R.β i) (R.junction_geodesic (i + 1))
        ⟨by linarith [R.δ_pos (i + 1)], R.δ_pos (i + 1)⟩
        (R.junction_right i hi).self_of_nhds.2
        (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
        (fun s => (hasDerivAt_id s).prodMk (hasDerivAt_const s (R.τ (i + 1))))
        ((R.junction_right i hi).mono fun _ h => h.1)
  have hnonneg := sum_nonneg_of_isLocalMin R.ε_pos hfirst hsecond hlocal
  convert hnonneg using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply intervalIntegral.integral_congr
  intro t ht
  have hi' := Finset.mem_range.mp hi
  have ht' : t ∈ Icc (R.τ i) (R.τ (i + 1)) := by
    simpa only [uIcc_of_le (R.strict i).le] using ht
  have hqt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo
    (hsub (R.time_subset hi' ht'))
  have hVa := contDiffAt_chartField_change hqt (mem_extChartAt_source _) (R.source hi' ht')
    (hV t (hsub (R.time_subset hi' ht')))
  exact (chartIndexIntegrand_eq_intrinsic g D (R.β i) hqt (R.source hi' ht')
    (hVa.differentiableAt (by simp))
    (((R.smooth i hi').of_le (by norm_num)).contDiffAt)
    (R.base i hi' t ht') (R.field i hi' t ht')).symm

theorem GeodesicVariation.index_integrable [T2Space M]
    (R : GeodesicVariation g γ V a b η₀ η₁) (D : LeviCivitaData g)
    {I : Set ℝ} (hsub : Icc a b ⊆ I) (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    (i : ℕ) (hi : i < R.N) :
    IntervalIntegrable (intrinsicIndexIntegrand g D γ V)
      MeasureTheory.volume (R.τ i) (R.τ (i + 1)) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (R.strict i).le]
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) (R.β i)).symm
  let A := christoffelBilinear B
  have hG : ContDiffOn ℝ 2 B (extChartAt (𝓡 n) (R.β i)).target :=
    (g.contDiffOn_chartCoefficients (R.β i)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hA : ContDiffOn ℝ 1 A (extChartAt (𝓡 n) (R.β i)).target := by
    intro x hx
    have hAx : ContDiffAt ℝ ∞ A x := contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients (R.β i)).contDiffAt
        ((isOpen_extChartAt_target (R.β i)).mem_nhds hx))
      (g.isInvertible_chartCoefficients (R.β i) hx)
    exact (hAx.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).contDiffWithinAt
  have hc := continuousOn_chartIndexIntegrand
    (isOpen_extChartAt_target (R.β i)) hG hA (R.smooth i hi)
    (J := Icc (R.τ i) (R.τ (i + 1)))
    (fun t ht => R.tube i hi (0, t) ⟨⟨by linarith [R.ε_pos], R.ε_pos⟩,
      ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩⟩)
  apply hc.congr
  intro t ht
  have hqt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo
    (hsub (R.time_subset hi ht))
  have hVa := contDiffAt_chartField_change hqt (mem_extChartAt_source _) (R.source hi ht)
    (hV t (hsub (R.time_subset hi ht)))
  exact (chartIndexIntegrand_eq_intrinsic g D (R.β i) hqt (R.source hi ht)
    (hVa.differentiableAt (by simp))
    (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
    (R.base i hi t ht) (R.field i hi t ht)).symm

end PoincareConjecture.Synge
