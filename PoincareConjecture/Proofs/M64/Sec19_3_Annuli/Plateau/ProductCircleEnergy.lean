import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseLift
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem m64CirclePhase_column_sq_le_gram (P : M62.CircleProductData F circumference)
    (t : ℝ) (f : LoopPlane → P.charts.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f)
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L)
    (hquot : ∀ p, P.circle.quotient (L p) = (f p).2) (p : LoopPlane) (i : Fin 2) :
    (fderiv ℝ L p (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2 ≤
      m60AreaGram (P.flow.metric t) f p i i := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let v : LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ i
  let W := mfderiv (𝓡 2) (𝓡 (n + 1)) f p v
  have hsnd : MDifferentiable (𝓡 (n + 1)) (𝓡 1)
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  have hpr := mfderiv_comp_apply (f := f)
    (g := (Prod.snd : P.charts.Point → P.circle.Point)) p (hsnd (f p))
    (hf.mdifferentiable (by simp) p) v
  have hl := mfderiv_comp_apply (f := L) (g := P.circle.quotient) p
    (P.circle.quotient_smooth.mdifferentiableAt (by simp))
    ((hL.differentiable (by simp) p).hasFDerivAt.hasMFDerivAt.mdifferentiableAt) v
  have heq : P.circle.quotient ∘ L = Prod.snd ∘ f := funext hquot
  rw [heq, mfderiv_eq_fderiv] at hl
  have hv : (P.charts.split (f p) W).2 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L p) (fderiv ℝ L p v) := by
    rw [P.charts.split_circle]
    exact hpr.symm.trans hl
  have hcircle : P.circle.metricOnPoints.inner (f p).2
      (P.charts.split (f p) W).2 (P.charts.split (f p) W).2 = (fderiv ℝ L p v) ^ 2 := by
    rw [hv, ← hquot p]
    simpa +instances only [M62.CircleGeometry.quotient, M62.CircleGeometry.metricOnPoints,
      pow_two] using! P.circle.metric_quotient (L p) (fderiv ℝ L p v) (fderiv ℝ L p v)
  have hbase : 0 ≤ (F.metric t).inner (f p).1
      (P.charts.split (f p) W).1 (P.charts.split (f p) W).1 :=
    (F.metric t).toRiemannianMetric.toCore (f p).1 |>.re_inner_nonneg _
  change (fderiv ℝ L p v) ^ 2 ≤ (P.flow.metric t).inner (f p) W W
  rw [P.metric_eq, hcircle]
  linarith



theorem m64CirclePhase_energy_lower_bound (P : M62.CircleProductData F circumference)
    (t : ℝ) (f : LoopPlane → P.charts.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 (n + 1)) 1 f)
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L)
    (hquot : ∀ p, P.circle.quotient (L p) = (f p).2)
    {d : ℝ} (hshift : ∀ x s,
      L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d) :
    d ^ 2 ≤ 2 * curvePeriod * ∫ p in interior m64AnnulusDomain,
      m60EnergyDensity (P.flow.metric t) f p := by
  have hpoint (p : LoopPlane) :
      (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2 ≤
        2 * m60EnergyDensity (P.flow.metric t) f p := by
    have hcol := m64CirclePhase_column_sq_le_gram P t f hf L hL hquot p 0
    have hnonneg := m60AreaGram_diagonal_nonneg (P.flow.metric t) f p 1
    simp only [EuclideanSpace.basisFun_apply] at hcol
    unfold m60EnergyDensity
    rw [Matrix.trace_fin_two]
    linarith
  have hD : IntegrableOn (fun p =>
      (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2)
      (interior m64AnnulusDomain) volume :=
    (((hL.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hE : IntegrableOn (m60EnergyDensity (P.flow.metric t) f)
      (interior m64AnnulusDomain) volume :=
    (m60EnergyDensity_continuous _ hf).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hi := integral_mono hD (hE.const_mul 2) hpoint
  rw [integral_const_mul] at hi
  have hp : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hscale := mul_le_mul_of_nonneg_left hi hp
  have hphase := m64Annulus_phase_energy hL hshift
  nlinarith

end PoincareConjecture
