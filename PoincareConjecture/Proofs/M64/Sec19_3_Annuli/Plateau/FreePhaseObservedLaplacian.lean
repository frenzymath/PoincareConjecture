import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalHarmonicObservationBound
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedClassicalEnergyBound
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseHarmonicCharts











noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain





theorem auxiliaryCircle_free_phase_observed_laplacian_growth
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → E)
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e) (hei : Topology.IsEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (Robs : E →L[ℝ] LoopPlane) (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point) (LC : LeviCivitaData g)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Continuous B) {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (hA : ContinuousOn A.annulus.map S) :
    let D := m64SourceScale (Real.sqrt modulus) (Real.sqrt_pos.mpr hmodulus).ne'
    let f := e ∘ (A.annulus.map ∘ D)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ D ⁻¹' S,
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ f) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ f p (EuclideanSpace.single i 1)‖ ^ 2 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let D := m64SourceScale (Real.sqrt modulus) (Real.sqrt_pos.mpr hmodulus).ne'
  let f := A.annulus.map ∘ D
  obtain ⟨C0, hC0, hgrowth⟩ := m64LocalHarmonic_observation_vector_bound LC he
  refine ⟨C0 * (max bound 0 / 2), by positivity, fun p hp => ?_⟩
  obtain ⟨q, u, R, hR, -, hus, hut, hmap, hharm⟩ :=
    auxiliaryCircle_free_phase_rescaled_harmonic_chart P Q e (he.of_le (by simp)) hei
      hread Robs hRobs A g B hB hb hdiag hmodulus hminimum hA hp
  have hpB : p ∈ D ⁻¹' ball (D p) R := by
    change D p ∈ ball (D p) R
    exact mem_ball_self hR
  have hU : IsOpen (D ⁻¹' ball (D p) R) := isOpen_ball.preimage D.continuous
  have hu2 : ContDiffAt ℝ 2 (u ∘ D) p :=
    (hus.contDiffAt (hU.mem_nhds hpB)).of_le (WithTop.coe_le_coe.mpr le_top)
  have htarget : (u ∘ D) p ∈ (extChartAt (𝓡 ((n + 1) + 1)) q).target :=
    hut (mem_closedBall_self hR.le)
  have heq : ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ (u ∘ D)) =ᶠ[𝓝 p] f := by
    filter_upwards [hU.mem_nhds hpB] with z hz
    exact hmap (ball_subset_closedBall hz)
  have hraw := hgrowth q (u ∘ D) f p hu2 htarget heq (hharm p hpB)
  have hcs := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds htarget)
  have hf : MDifferentiableAt (𝓡 2) (𝓡 ((n + 1) + 1)) f p :=
    ((hcs.mdifferentiableAt (by simp)).comp p
      (hu2.contMDiffAt.mdifferentiableAt (by norm_num))).congr_of_eventuallyEq heq.symm
  have henergy := m64ObservedMetric_energyDensity_le_columns g e (he.of_le (by simp))
    B hdiag hf ((hb (f p)).trans (le_max_left bound 0))
  simp only [EuclideanSpace.basisFun_apply] at hraw
  exact hraw.trans ((mul_le_mul_of_nonneg_left henergy hC0).trans_eq (by ring))

end PoincareConjecture.M64
