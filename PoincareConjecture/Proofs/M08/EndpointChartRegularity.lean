import PoincareConjecture.Proofs.M08.ClosedChartCoefficients
import PoincareConjecture.Proofs.M08.EndpointMomentum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance endpointChartRegularityDualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance endpointChartRegularityDualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance endpointChartRegularityBilinNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance endpointChartRegularityBilinNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in
theorem endpoint_chart_phase_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) {a b : ℝ}
    (hab : a < b) (u d : ℝ → EuclideanSpace ℝ (Fin n))
    (hu : ContinuousOn u (Icc a b))
    (hud : ∀ s ∈ Ioo a b, HasDerivAt u (d s) s)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (htarget : MapsTo u (Icc a b) (extChartAt (𝓡 n) x).target)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (hmomentum : ∀ s ∈ Ioo a b,
      HasDerivAt (fun r ↦ chartMetricOperator F T x (r, u r) (d r))
        (chartForceVector
          (spatialWithinFDeriv (Icc a b) (extChartAt (𝓡 n) x).target
            (chartActionMetric F T x) (s, u s))
          (spatialWithinFDeriv (Icc a b) (extChartAt (𝓡 n) x).target
            (chartActionPotential F T x) (s, u s)) (d s)) s) :
    ∃ Pbar : ℝ → EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ (fun s ↦ (u s, Pbar s)) (Icc a b) ∧
      EqOn Pbar (fun s ↦ chartMetricOperator F T x (s, u s) (d s)) (Ioo a b) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt (fun r ↦ (u r, Pbar r))
        (closedChartEulerPhase F T x (Icc a b) s (u s, Pbar s)) (Icc a b) s := by
  let G := fun s ↦ chartActionMetric F T x (s, u s)
  let DG := fun s ↦ spatialWithinFDeriv (Icc a b) (extChartAt (𝓡 n) x).target
    (chartActionMetric F T x) (s, u s)
  let DV := fun s ↦ spatialWithinFDeriv (Icc a b) (extChartAt (𝓡 n) x).target
    (chartActionPotential F T x) (s, u s)
  let A := fun s ↦ chartMetricOperator F T x (s, u s)
  let B := fun s ↦ Ring.inverse (A s)
  let P := fun s ↦ A s (d s)
  let Q := fun s ↦ chartForceVector (DG s) (DV s) (d s)
  have hpair : ContinuousOn (fun s ↦ (s, u s)) (Icc a b) :=
    continuousOn_id.prodMk hu
  have hmap : MapsTo (fun s ↦ (s, u s)) (Icc a b)
      (Icc a b ×ˢ (extChartAt (𝓡 n) x).target) :=
    fun s hs ↦ ⟨hs, htarget hs⟩
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x
  have hG : ContinuousOn G (Icc a b) :=
    (chartActionMetric_closed_contDiffOn F T x htime).continuousOn.comp hpair hmap
  have hDG : ContinuousOn DG (Icc a b) :=
    (spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU _
      (chartActionMetric_closed_contDiffOn F T x htime)).continuousOn.comp hpair hmap
  have hDV : ContinuousOn DV (Icc a b) :=
    (spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU _
      (chartActionPotential_closed_contDiffOn F hM04 T x htime)).continuousOn.comp hpair hmap
  have hB : ContinuousOn B (Icc a b) :=
    (chartMetricInverse_closed_contDiffOn F T x htime).continuousOn.comp hpair hmap
  have hinv (s : ℝ) (hs : s ∈ Icc a b) (v : EuclideanSpace ℝ (Fin n)) :
      B s (A s v) = v :=
    inverse_operator_apply _ (chartMetricOperator_isUnit_of_target F T x (htarget hs)) v
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hDG
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hDV
  let C := |C₀| + |C₁| + |C₂|
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound : ∀ s ∈ Icc a b, ‖G s‖ ≤ C ∧ ‖DG s‖ ≤ C ∧ ‖DV s‖ ≤ C := by
    intro s hs
    have h₀ := hC₀ s hs
    have h₁ := hC₁ s hs
    have h₂ := hC₂ s hs
    dsimp only [C]
    refine ⟨?_, ?_, ?_⟩ <;>
      linarith [le_abs_self C₀, le_abs_self C₁, le_abs_self C₂,
        abs_nonneg C₀, abs_nonneg C₁, abs_nonneg C₂]
  have hQ : IntervalIntegrable Q volume a b :=
    (chart_momentum_force_intervalIntegrable hab.le hC d hd G DG DV hG hDG hDV hbound).2
  obtain ⟨c, q, Pbar, hPbar, hq, hPc, hqc, hPeq, hqeq, _, hudbar, _⟩ :=
    endpoint_velocity_of_momentum hab u d P Q hu hud hd A B hB hinv
      (fun _ _ ↦ rfl) hQ hmomentum
  let Qbar := fun s ↦ chartForceVector (DG s) (DV s) (q s)
  have hQbar : ContinuousOn Qbar (Icc a b) :=
    chartForceVector_continuousOn hDG hDV hqc
  have hQeq : EqOn Qbar Q (Ioo a b) := by
    intro s hs
    dsimp only [Qbar, Q]
    rw [hqeq hs]
  have hPdbar (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt Pbar (Qbar s) (Icc a b) s := by
    rw [show Pbar = (fun r ↦ c + ∫ t in a..r, Q t) from funext hPbar]
    exact endpoint_momentum_derivative_of_continuous_force hab c Q Qbar hQeq hQbar s hs
  have hinvq (s : ℝ) :
      Ring.inverse (chartMetricOperator F T x (s, u s)) (Pbar s) = q s :=
    (hq s).symm
  have hphase (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun r ↦ (u r, Pbar r))
        (closedChartEulerPhase F T x (Icc a b) s (u s, Pbar s)) (Icc a b) s := by
    simpa only [closedChartEulerPhase, hinvq s, Qbar, DG, DV] using
      (hudbar s hs).prodMk (hPdbar s hs)
  have hphasemem : MapsTo (fun s ↦ (u s, Pbar s)) (Icc a b)
      ((extChartAt (𝓡 n) x).target ×ˢ univ) :=
    fun s hs ↦ ⟨htarget hs, mem_univ _⟩
  have hsmooth := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
    (closedChartEulerPhase_contDiffOn F hM04 T x (uniqueDiffOn_Icc hab) htime)
      hphase hphasemem
  exact ⟨Pbar, hsmooth, hPeq, hphase⟩

end PoincareConjecture.M08
