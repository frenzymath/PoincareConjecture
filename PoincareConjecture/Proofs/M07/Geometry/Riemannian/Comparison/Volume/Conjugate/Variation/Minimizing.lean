import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Geodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.PieceDeriv
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Broken
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.MinimalVariation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.Conjugate.Realization

open CoordinateExponential ConnectionVariation ConnectionAlongCurve ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {γ : ℝ → M}
  {V₀ V₁ : ℝ → EuclideanSpace ℝ (Fin n)} {a c b : ℝ}

private theorem BrokenRealization.source
    (R : BrokenRealization g γ V₀ V₁ a c b)
    {i : ℕ} (hi : i < R.N) {t : ℝ} (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
    γ t ∈ (extChartAt (𝓡 n) (R.β i)).source :=
  R.base_source i hi t ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩

private theorem BrokenRealization.time_subset
    (R : BrokenRealization g γ V₀ V₁ a c b)
    {i : ℕ} (hi : i < R.N) : Icc (R.τ i) (R.τ (i + 1)) ⊆ Icc a b := by
  intro t ht
  exact ⟨(R.time_mem i (by omega)).1.trans ht.1,
    ht.2.trans (R.time_mem (i + 1) (by omega)).2⟩



theorem BrokenRealization.sum_index_nonneg [T2Space M]
    (R : BrokenRealization g γ V₀ V₁ a c b) (D : LeviCivitaData g)
    {I : Set ℝ} (hsub : Icc a b ⊆ I) (hgeo : g.IsGeodesicOn γ I)
    (hV₀ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₀) t)
    (hV₁ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₁) t)
    {C : ℝ} (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc a b, g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C)
    (hmin : g.edist (γ a) (γ b) = ENNReal.ofReal ((b - a) * C)) :
    0 ≤ ∑ i ∈ Finset.range R.N, ∫ t in (R.τ i)..(R.τ (i + 1)),
      intrinsicIndexIntegrand g D γ (if i < R.k then V₀ else V₁) t := by
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
  obtain ⟨l, r, hlr, hwindow⟩ := hjunction.exists_Ioo_subset
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
    Poincare.VolumeComparison.Conjugate.isLocalMin_sum_chartEnergy g R.τ R.β R.u R.η
      hε hC hτ R.smooth
      (fun s hs i hi t ht => R.tube i hi (s, t)
        ⟨hsmall hs, ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩⟩)
      (fun _ hs i hi => (hj hs i hi).1) (fun _ hs i hi => (hj hs i hi).2)
      (fun s _ => by simpa only [R.fixed_left, R.fixed_right, R.left, R.right] using hmin)
      hzero
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
  have hqt := contMDiffAt_of_isGeodesicOn hgeo (hsub (R.time_subset hi' ht'))
  have hV : ContDiffAt ℝ ∞ (chartField γ (γ t) (if i < R.k then V₀ else V₁)) t := by
    split_ifs
    · exact hV₀ t (hsub (R.time_subset hi' ht'))
    · exact hV₁ t (hsub (R.time_subset hi' ht'))
  have hVa := contDiffAt_chartField_change hqt (mem_extChartAt_source _) (R.source hi' ht') hV
  exact (chartIndexIntegrand_eq_intrinsic g D (R.β i) hqt (R.source hi' ht')
    (hVa.differentiableAt (by simp))
    (((R.smooth i hi').of_le (by norm_num)).contDiffAt)
    (R.base i hi' t ht') (R.field i hi' t ht')).symm

private theorem BrokenRealization.index_integrable [T2Space M]
    (R : BrokenRealization g γ V₀ V₁ a c b) (D : LeviCivitaData g)
    {I : Set ℝ} (hsub : Icc a b ⊆ I) (hgeo : g.IsGeodesicOn γ I)
    (hV₀ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₀) t)
    (hV₁ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₁) t)
    (i : ℕ) (hi : i < R.N) :
    IntervalIntegrable (intrinsicIndexIntegrand g D γ (if i < R.k then V₀ else V₁))
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
  have hqt := contMDiffAt_of_isGeodesicOn hgeo (hsub (R.time_subset hi ht))
  have hV : ContDiffAt ℝ ∞ (chartField γ (γ t) (if i < R.k then V₀ else V₁)) t := by
    split_ifs
    · exact hV₀ t (hsub (R.time_subset hi ht))
    · exact hV₁ t (hsub (R.time_subset hi ht))
  have hVa := contDiffAt_chartField_change hqt (mem_extChartAt_source _) (R.source hi ht) hV
  exact (chartIndexIntegrand_eq_intrinsic g D (R.β i) hqt (R.source hi ht)
    (hVa.differentiableAt (by simp))
    (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
    (R.base i hi t ht) (R.field i hi t ht)).symm




theorem index_nonneg_of_minimizing [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {γ : ℝ → M} {V₀ V₁ : ℝ → EuclideanSpace ℝ (Fin n)} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) {I : Set ℝ} (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hgeo : g.IsGeodesicOn γ I)
    (hV₀ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₀) t)
    (hV₁ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V₁) t)
    (hmatch : V₀ c = V₁ c) (hleft : V₀ a = 0) (hright : V₁ b = 0)
    {C : ℝ} (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc a b, g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C)
    (hmin : g.edist (γ a) (γ b) = ENNReal.ofReal ((b - a) * C)) :
    0 ≤ (∫ t in a..c, intrinsicIndexIntegrand g D γ V₀ t) +
      ∫ t in c..b, intrinsicIndexIntegrand g D γ V₁ t := by
  classical
  obtain ⟨R⟩ := exists_broken_realization g hac hcb hI hsub hgeo hV₀ hV₁ hmatch hleft hright
  have hnonneg := R.sum_index_nonneg D hsub hgeo hV₀ hV₁ hC hspeed hmin
  have hsum : (∑ i ∈ Finset.range R.N, ∫ t in (R.τ i)..(R.τ (i + 1)),
      intrinsicIndexIntegrand g D γ (if i < R.k then V₀ else V₁) t) =
        (∫ t in a..c, intrinsicIndexIntegrand g D γ V₀ t) +
          ∫ t in c..b, intrinsicIndexIntegrand g D γ V₁ t := by
    rw [← Finset.sum_range_add_sum_Ico _ R.k_lt.le]
    have hleft : (∑ i ∈ Finset.range R.k, ∫ t in (R.τ i)..(R.τ (i + 1)),
        intrinsicIndexIntegrand g D γ (if i < R.k then V₀ else V₁) t) =
          ∫ t in (R.τ 0)..(R.τ R.k), intrinsicIndexIntegrand g D γ V₀ t := by
      calc
        _ = ∑ i ∈ Finset.range R.k, ∫ t in (R.τ i)..(R.τ (i + 1)),
            intrinsicIndexIntegrand g D γ V₀ t := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (Finset.mem_range.mp hi)]
        _ = _ := intervalIntegral.sum_integral_adjacent_intervals fun i hi => by
          simpa only [if_pos hi] using
            R.index_integrable D hsub hgeo hV₀ hV₁ i (hi.trans R.k_lt)
    have hright : (∑ i ∈ Finset.Ico R.k R.N, ∫ t in (R.τ i)..(R.τ (i + 1)),
        intrinsicIndexIntegrand g D γ (if i < R.k then V₀ else V₁) t) =
          ∫ t in (R.τ R.k)..(R.τ R.N), intrinsicIndexIntegrand g D γ V₁ t := by
      calc
        _ = ∑ i ∈ Finset.Ico R.k R.N, ∫ t in (R.τ i)..(R.τ (i + 1)),
            intrinsicIndexIntegrand g D γ V₁ t := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_neg (not_lt.mpr (Finset.mem_Ico.mp hi).1)]
        _ = _ := intervalIntegral.sum_integral_adjacent_intervals_Ico R.k_lt.le fun i hi => by
          simpa only [if_neg (not_lt.mpr hi.1)] using
            R.index_integrable D hsub hgeo hV₀ hV₁ i hi.2
    rw [hleft, hright, R.left, R.corner, R.right]
  simpa only [hsum] using hnonneg

end PoincareConjecture.Conjugate.Realization
