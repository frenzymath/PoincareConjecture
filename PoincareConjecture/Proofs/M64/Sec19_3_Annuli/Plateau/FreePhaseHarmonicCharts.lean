import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseInteriorSmooth
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitStrongEquation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak CoordinateExponential ConnectionVariation
  ConjugateVariation

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))




theorem auxiliaryCircle_free_phase_rescaled_harmonic_chart
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
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (hA : ContinuousOn A.annulus.map S) {p0 : LoopPlane} (hp0 : p0 ∈ S) :
    let D := m64SourceScale (Real.sqrt modulus) (Real.sqrt_pos.mpr hmodulus).ne'
    ∃ (q : Q.charts.Point) (u : LoopPlane → E) (R : ℝ),
      0 < R ∧ closedBall p0 R ⊆ S ∧
      ContDiffOn ℝ ∞ (u ∘ D) (D ⁻¹' ball p0 R) ∧
      MapsTo u (closedBall p0 R) (extChartAt (𝓡 ((n + 1) + 1)) q).target ∧
      EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
        A.annulus.map (closedBall p0 R) ∧
      ∀ p ∈ D ⁻¹' ball p0 R, (∑ i : Fin 2,
        covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 ((n + 1) + 1)) q).symm)) (u ∘ D)
          (fun z => fderiv ℝ (u ∘ D) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0 := by
  let s := Real.sqrt modulus
  let D := m64SourceScale s (Real.sqrt_pos.mpr hmodulus).ne'
  obtain ⟨q, L, R, hR, hRS, hchart, hu0, -, hW, hw⟩ :=
    A.annulus.exists_local_chart_columns he.continuous hread hA hp0
  obtain ⟨u, hu, heq⟩ := m64_exists_continuous_extension isClosed_closedBall hu0
  have hcoord (p : LoopPlane) (hp : p ∈ closedBall p0 R) :
      u p = extChartAt (𝓡 ((n + 1) + 1)) q (A.annulus.map p) :=
    (heq hp).trans (hchart p hp).2
  have huT : MapsTo u (closedBall p0 R) (extChartAt (𝓡 ((n + 1) + 1)) q).target := by
    intro p hp
    rw [hcoord p hp]
    exact (extChartAt (𝓡 ((n + 1) + 1)) q).map_source (hchart p hp).1
  have hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall p0 R) := by
    intro p hp
    change (extChartAt (𝓡 ((n + 1) + 1)) q).symm (u p) = A.annulus.map p
    rw [hcoord p hp, (extChartAt (𝓡 ((n + 1) + 1)) q).left_inv (hchart p hp).1]
  have hwu (i : Fin 2) (j : Fin ((n + 1) + 1)) : HasWeakPartialDeriv i
      (fun p => L (A.annulus.column i p) j) (fun p => u p j) (ball p0 R) := by
    apply m64WeakPartialDeriv_ae_congr ?_ (Eventually.of_forall fun _ => rfl) (hw i j)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hp
    exact congrArg (fun v : E => v j) (heq (ball_subset_closedBall hp)).symm
  have hlocal (p : LoopPlane) (hp : p ∈ ball p0 R) :
      ContDiffAt ℝ ∞ (u ∘ D) (D.symm p) ∧ (∑ i : Fin 2,
        covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 ((n + 1) + 1)) q).symm)) (u ∘ D)
          (fun z => fderiv ℝ (u ∘ D) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) (D.symm p)) = 0 := by
    obtain ⟨rho, hrho, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (isOpen_ball.mem_nhds hp)
    have hsmallR : closedBall p rho ⊆ closedBall p0 R :=
      hsmall.trans ball_subset_closedBall
    have hsmallB : ball p rho ⊆ ball p0 R := ball_subset_closedBall.trans hsmall
    obtain ⟨radius, hcritical⟩ := auxiliaryCircle_free_phase_rescaled_critical
      P Q e he hei Robs hRobs A g B hB hb hdiag hmodulus hminimum
      q hrho (hsmallR.trans hRS) hu (fun z hz => huT (hsmallR hz))
      (fun i => (hW i).mono_measure (Measure.restrict_mono hsmallB le_rfl))
      (fun i j => (hwu i j).restrict isOpen_ball hsmallB)
      (fun z hz => hmap (hsmallR hz))
    have hsm := M60.suWeakAlphaCoordinate_smooth_alpha_one g q (u ∘ D)
      (fun i z => m64SourceScaleFactor s i • L (A.annulus.column i (D z)))
      (D.symm p) radius hcritical
    exact ⟨hsm, M60.suWeakAlphaCoordinate_harmonic_of_smooth hcritical hsm⟩
  refine ⟨q, u, R, hR, hRS, ?_, huT, hmap, ?_⟩
  · intro p hp
    have h := (hlocal (D p) hp).1
    rw [D.symm_apply_apply] at h
    exact h.contDiffWithinAt
  · intro p hp
    have h := (hlocal (D p) hp).2
    simpa only [D.symm_apply_apply] using h

end PoincareConjecture.M64
