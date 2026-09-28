import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseHarmonicCharts
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceScaleStress













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain




theorem auxiliaryCircle_free_phase_stress_cauchyRiemann
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {r : ℝ} (hr : 0 < r)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B r)
    (hA : ContinuousOn A.annulus.map S) {p : LoopPlane} (hp : p ∈ S) :
    let G := m60AreaGram g A.annulus.map
    let U := fun z => r * G z 0 0 - r⁻¹ * G z 1 1
    let W := fun z => -2 * G z 0 1
    let v := EuclideanSpace.basisFun (Fin 2) ℝ
    fderiv ℝ U p (v 0) = r⁻¹ * fderiv ℝ W p (v 1) ∧
      fderiv ℝ U p (v 1) = -r * fderiv ℝ W p (v 0) := by
  have hsm := auxiliaryCircle_free_phase_contMDiffOn
    P Q e he hei hread Robs hRobs A g B hB hb hdiag hr hminimum hA
  apply m64WeightedStress_of_rescaled g isOpen_interior hsm hp hr
  let D := m64SourceScale (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne'
  obtain ⟨q, u, R, hR, -, hu, hut, hmap, hharm⟩ :=
    auxiliaryCircle_free_phase_rescaled_harmonic_chart
      P Q e he hei hread Robs hRobs A g B hB hb hdiag hr hminimum hA hp
  have hpt : D.symm p ∈ D ⁻¹' ball p R := by
    simpa only [mem_preimage, D.apply_symm_apply] using mem_ball_self hR
  apply m64LocalHarmonicMap_stress_cauchyRiemann g q
    (isOpen_ball.preimage D.continuous) hu
    (fun z hz => hut (ball_subset_closedBall hz)) ?_ hpt (hharm _ hpt)
  intro z hz
  exact hmap (ball_subset_closedBall hz)

end PoincareConjecture.M64
