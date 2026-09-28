import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

set_option maxHeartbeats 2400000 in

theorem exists_variational_chart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (heinj : Function.Injective e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (q : LoopPlane → M)
    (hqcont : ContinuousOn q U) (hq : q =ᵐ[volume.restrict U] F.value)
    {x : LoopPlane} (hx : x ∈ U) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ closedBall x (8 * R) ⊆ U ∧
      ∃ (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (_DE : LeviCivitaData gE)
        (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) (ball x (8 * R))),
        (∀ z, X.value z = extChartAt (𝓡 3) (q x) (q z)) ∧
        (∀ z ∈ ball x (8 * R), q z ∈ (extChartAt (𝓡 3) (q x)).source) ∧
        MapsTo X.value (ball x (8 * R))
          (ball (extChartAt (𝓡 3) (q x) (q x)) (ε / 2)) ∧
        (∀ y ∈ ball (extChartAt (𝓡 3) (q x) (q x)) ε,
          y ∈ (extChartAt (𝓡 3) (q x)).target ∧
            ∀ v w : EuclideanSpace ℝ (Fin 3), gE.inner y v w =
              g.inner ((extChartAt (𝓡 3) (q x)).symm y)
                (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q x)).symm y v)
                (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q x)).symm y w)) ∧
        (∀ i, F.derivative i =ᵐ[volume.restrict (ball x (8 * R))] fun z =>
          fderiv ℝ (e ∘ (extChartAt (𝓡 3) (q x)).symm)
            (extChartAt (𝓡 3) (q x) (q z)) (X.derivative i z)) ∧
        ∀ (V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)), ContDiff ℝ 1 V →
          ∀ CV : NNReal, (∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ)) →
            ∀ (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ ball x R →
              ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
                (∫ z in closedBall x (2 * R), coordinateHalfEnergy gE X.value X.derivative z) ≤
                  ∫ z in closedBall x (2 * R), coordinateHalfEnergy gE
                    (variationValue X.value V φ t)
                    (variationField X.value X.derivative V φ t) z := by
  let c := extChartAt (𝓡 3) (q x)
  let a := c (q x)
  obtain ⟨R0, hR0, hR0U, X0, hX0, hsource0, hfield0⟩ :=
    exists_chart_graph e he hinj hU F q hqcont hq hx
  obtain ⟨B, CB, W, hB, hCB, hWo, haW, hWt, hBeq⟩ :=
    exists_inverse_chart_extension e he (q x)
  obtain ⟨gE, DE, hmetric⟩ := m65Exists_chartMetric g (q x)
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (hWo.mem_nhds haW) hmetric)
  have hεtarget (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ ball a ε) : y ∈ c.target :=
    hWt (hεW hy).1
  have hcq : ContinuousAt (fun z => c (q z)) x :=
    (contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞)).continuousAt.comp
      (hqcont.continuousAt (hU.mem_nhds hx))
  have hnear : ∀ᶠ z in 𝓝 x, X0.value z ∈ ball a (ε / 2) := by
    filter_upwards [hcq.eventually (ball_mem_nhds a (half_pos hε))] with z hz
    rw [hX0 z]
    exact hz
  obtain ⟨η, hη, hηcap⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (ball_mem_nhds x hR0) hnear)
  let R := η / 16
  have hR : 0 < R := by dsimp only [R]; positivity
  have h8η : closedBall x (8 * R) ⊆ ball x η :=
    closedBall_subset_ball (by dsimp only [R]; linarith)
  have h8R0 : closedBall x (8 * R) ⊆ ball x R0 := fun z hz => (hηcap (h8η hz)).1
  have h8U : closedBall x (8 * R) ⊆ U := h8R0.trans (ball_subset_closedBall.trans hR0U)
  have hb8R0 := ball_subset_closedBall.trans h8R0
  let X := restrict_map X0 hb8R0
  have hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)) :=
    fun z hz => (hηcap (h8η (ball_subset_closedBall hz))).2
  have hXbig (z : LoopPlane) (hz : z ∈ ball x (8 * R)) : X.value z ∈ ball a ε :=
    ball_subset_ball (by linarith) (hXcap hz)
  have hBψ (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ ball a ε) : e (c.symm y) = B y :=
    (hBeq y (hεW hy).1).1.symm
  have hfield (i : Fin 2) : F.derivative i =ᵐ[volume.restrict (ball x (8 * R))]
      fun z => fderiv ℝ (e ∘ c.symm) (c (q z)) (X.derivative i z) :=
    ae_restrict_of_ae_restrict_of_subset hb8R0 (hfield0 i)
  have hvalueB : (fun z => B (X.value z)) =ᵐ[volume.restrict (ball x (8 * R))]
      fun z => e (F.value z) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_closedBall.trans h8U) hq, ae_restrict_mem measurableSet_ball] with z hz hzs
    rw [← hBψ _ (hXbig z hzs)]
    change e (c.symm (X0.value z)) = e (F.value z)
    rw [hX0 z, c.left_inv (hsource0 z (hb8R0 hzs)), hz]
  have hfieldB (i : Fin 2) : (fun z => fderiv ℝ B (X.value z) (X.derivative i z))
      =ᵐ[volume.restrict (ball x (8 * R))] F.derivative i := by
    filter_upwards [hfield i, ae_restrict_mem measurableSet_ball] with z hz hzs
    rw [(hBeq _ (hεW (hXbig z hzs)).1).2]
    change fderiv ℝ (e ∘ c.symm) (X0.value z) (X.derivative i z) = F.derivative i z
    rw [hX0 z]
    exact hz.symm
  have hpair (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ ball a ε)
      (v w : EuclideanSpace ℝ (Fin 3)) :
      m65EmbeddingMetric g e (c.symm y) (fderiv ℝ B y v) (fderiv ℝ B y w) = gE.inner y v w := by
    have hψ : MDifferentiableAt (𝓡 3) (𝓡 3) c.symm y :=
      ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) (q x) (hεtarget y hy)).contMDiffAt
        (extChartAt_target_mem_nhds' (hεtarget y hy))).mdifferentiableAt (by simp)
    rw [(hBeq y (hεW hy).1).2, reconstruction_pairing g e c.symm y
      (he.contMDiffAt.mdifferentiableAt (by simp)) hψ (hinj _) v w]
    exact ((hεW hy).2 v w).symm
  refine ⟨R, ε, hR, hε, h8U, gE, DE, X, hX0, ?_, hXcap, ?_, hfield, ?_⟩
  · intro z hz
    exact hsource0 z (hb8R0 hz)
  · intro y hy
    exact ⟨hεtarget y hy, (hεW hy).2⟩
  · intro V hV CV hCV φ hc hs
    exact captured_energy_comparison heinj g F hmin x hR
      ((closedBall_subset_closedBall (by linarith)).trans h8U)
      X c.symm B hB CB hCB a hε hXcap hBψ hvalueB hfieldB gE hpair V hV CV hCV φ hc hs

end PoincareConjecture.M65Euler
