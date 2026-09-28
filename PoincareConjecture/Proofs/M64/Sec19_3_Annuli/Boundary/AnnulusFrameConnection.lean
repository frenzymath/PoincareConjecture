import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.OrdinaryChartDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripSourceNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ActualFrameConnection
import PoincareConjecture.Proofs.M64.Mathlib.LogScaledAffineDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace M65Gauss

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem annulus_chart_connection_log (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (x : ℝ) (upper : Bool)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    {R : ℝ} (hR1 : R < 1) :
    let a := annulusPoint x (if upper then 1 else 0)
    let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
    let P := annulusBoundarySource r hr.ne' upper x
    let H := q ∘ A.map ∘ P
    let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
    let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
    let V := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z))
      (halfDiskGradient H R z)
    let rho := fun p => m60AreaGram g A.map p 0 0
    MapsTo (A.map ∘ P) K q.source → ContDiffOn ℝ ∞ H W →
      (∀ z ∈ K, gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm) →
      (∀ z ∈ K, let L := fderivWithin ℝ H K z
        gE.inner (H z) (L 1) (L 1) = gE.inner (H z) (L I) (L I) ∧
          gE.inner (H z) (L 1) (L I) = 0) →
      ∀ z ∈ W, gE.inner (H z) (V z).1 (V z).1 = 1 →
        0 < rho (P z) ∧
        gE.inner (H z) (covariantDerivativeAlongMap DE H (fun w => (V w).1) z 1) (V z).2 =
          (if upper then 1 else -1) *
            fderiv ℝ (fun p => Real.log (rho p)) (P z)
              (EuclideanSpace.basisFun (Fin 2) ℝ 1) / 2 := by
  let a := annulusPoint x (if upper then 1 else 0)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
  let e := annulusBoundaryLinear r hr.ne' upper
  let P := annulusBoundarySource r hr.ne' upper x
  let H := q ∘ A.map ∘ P
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
  let rho := fun p => m60AreaGram g A.map p 0 0
  let lam := fun z => gE.inner (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1)
  change MapsTo (A.map ∘ P) K q.source → ContDiffOn ℝ ∞ H W → _
  intro hsource hH hmetric hconf z hz hunit
  have hWK : W ⊆ K := fun w hw =>
    ⟨ball_subset_closedBall hw.1, (show 0 < w.im from hw.2).le⟩
  have hPW := annulusBoundarySource_mapsTo_openStrip r x hr.ne' hR1 upper
  have hlam (w : ℂ) (hw : w ∈ W) : lam w = r ^ 2 * rho (P w) := by
    have hh := chart_affine_metric g (A.map a) e a
      ((hAi.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds (hPW hw))).mdifferentiableAt
        (by simp)) (hsource (hWK hw)) (hmetric w (hWK hw)).self_of_nhds 1 1
    rw [annulusBoundaryLinear_one] at hh
    simpa only [lam, H, Function.comp_def, P, annulusBoundarySource, e, a,
      rho, m60AreaGram, map_smul, smul_apply, smul_eq_mul, pow_two, mul_assoc] using hh
  obtain ⟨hpos, hconnection⟩ := halfDisk_actual_frame_connection_log DE hH hconf hz hunit
  have hrho : 0 < rho (P z) := by
    change 0 < lam z at hpos
    rw [hlam z hz] at hpos
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hr)).mp hpos
  have hEq : lam =ᶠ[𝓝 z] fun w => r ^ 2 * rho (P w) := by
    filter_upwards [(isOpen_ball.inter (isOpen_lt continuous_const continuous_im)).mem_nhds hz]
      with w hw
    exact hlam w hw
  have hD : DifferentiableAt ℝ rho (P z) :=
    (m64AreaGram_entry_contDiffAt
      (hAi.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds (hPW hz))) 0 0).differentiableAt
        (by simp)
  have hlog := log_scaled_affine_derivative e a (pow_ne_zero 2 hr.ne') hD hrho.ne' hEq I
  change fderiv ℝ (fun w => Real.log (lam w)) z I =
    fderiv ℝ (fun p => Real.log (rho p)) (P z) (e I) at hlog
  refine ⟨hrho, hconnection.trans ?_⟩
  change -fderiv ℝ (fun w => Real.log (lam w)) z I / 2 = _
  rw [hlog, annulusBoundaryLinear_I]
  cases upper <;> simp only [P, rho, Bool.false_eq_true, if_false, if_true, map_neg,
    neg_neg, one_mul, neg_one_mul]

end PoincareConjecture.M64
