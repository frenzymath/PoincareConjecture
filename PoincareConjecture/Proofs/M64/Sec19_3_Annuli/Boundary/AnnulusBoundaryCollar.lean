import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteAnnulusFrame
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusFrameConnection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ChartBoundaryCurvature






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace M65Gauss

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

set_option maxHeartbeats 1400000 in






theorem annulus_regular_boundary_collar (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (x : ℝ) (upper : Bool)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {c : ℝ → M} {sigma : ℝ → ℝ} (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ c)
    (hcv : ∀ s, curveVelocity (n := n) c s ≠ 0) (hsigma : ContDiff ℝ 1 sigma)
    (hmono : Monotone sigma)
    (htrace : ∀ s, A.map (annulusPoint s (if upper then 1 else 0)) = c (sigma s)) :
    let a := annulusPoint x (if upper then 1 else 0)
    let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
    let P := annulusBoundarySource r hr.ne' upper x
    let H := q ∘ A.map ∘ P
    let kappa := fun s => (g.tangentNorm (c s) (curveVelocity (n := n) c s))⁻¹ •
      rampHorizontalCovariantDerivative D c
        (fun y => (g.tangentNorm (c y) (curveVelocity (n := n) c y))⁻¹ •
          curveVelocity (n := n) c y) s
    let B := fun theta =>
      let p := annulusPoint theta (if upper then 1 else 0)
      g.inner (A.map p) (kappa (sigma theta))
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
      (d e C : ℝ) (V : ℂ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      0 < d ∧ d < 1 ∧ 0 < e ∧ 2 * e < d ∧ 0 ≤ C ∧
      let K := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) d ∩ {z | 0 < z.im}
      ContDiffOn ℝ 1 H K ∧ ContinuousOn V K ∧ ContDiffOn ℝ 1 V W ∧
      MemLp (fun z => fderiv ℝ V z 1) 2 (volume.restrict W) ∧
      (∀ z ∈ K, ∀ w ∈ K, ‖V z - V w‖ ≤ C * Real.sqrt ‖z - w‖) ∧
      (∀ z ∈ W,
        gE.inner (H z) (covariantDerivativeAlongMap DE H (fun w => (V w).1) z 1) (V z).2 =
          (if upper then 1 else -1) *
            fderiv ℝ (fun p => Real.log (m60AreaGram g A.map p 0 0)) (P z)
              (EuclideanSpace.basisFun (Fin 2) ℝ 1) / 2) ∧
      ∀ t ∈ Icc (-e) e, ContDiffAt ℝ 1 (fun s : ℝ => (V (s : ℂ)).1) t ∧
        gE.inner (H (t : ℂ))
          (deriv (fun s : ℝ => (V (s : ℂ)).1) t +
            connectionCoefficient DE (H (t : ℂ))
              (fderivWithin ℝ H K (t : ℂ) 1) (V (t : ℂ)).1) (V (t : ℂ)).2 =
          (if upper then -1 else 1) * B (x + r * t) := by
  let a := annulusPoint x (if upper then 1 else 0)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (A.map a)
  let P := annulusBoundarySource r hr.ne' upper x
  let H := q ∘ A.map ∘ P
  let kappa := fun s => (g.tangentNorm (c s) (curveVelocity (n := n) c s))⁻¹ •
    rampHorizontalCovariantDerivative D c
      (fun y => (g.tangentNorm (c y) (curveVelocity (n := n) c y))⁻¹ •
        curveVelocity (n := n) c y) s
  let B := fun theta =>
    let p := annulusPoint theta (if upper then 1 else 0)
    g.inner (A.map p) (kappa (sigma theta))
      (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  obtain ⟨gE, DE, R, d, hR, hR1, hd, hdR, hsrc, hH, hHi, hmetric, hconf, _heq,
      hV, hVi, hunit, hDF, _hDFI, ⟨C, hC, hholder⟩, _hT⟩ :=
    annulus_regular_boundary_frame A hr x upper hminimum hAc hAi hconformal hinj
      hc hcv hsigma hmono htrace
  let Q := halfDiskGradient H R
  let V := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
  let K := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  have hsub : K ⊆ closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter (closedBall_subset_closedBall hdR.le) Subset.rfl
  let label := fun t : ℝ => sigma (x + r * t)
  have hlabel : ContDiff ℝ 1 label :=
    hsigma.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hlabelmono : Monotone label := fun s t hst =>
    hmono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hr.le))
  have htr (t : ℝ) : A.map (P (t : ℂ)) = c (label t) := by
    dsimp only [P]
    rw [annulusBoundarySource_real]
    exact htrace (x + r * t)
  have hboundary := halfDisk_chart_boundary_connection D hAc (A.map a)
    (annulusBoundaryLinear r hr.ne' upper) a gE DE hd Q hc hcv hlabel (Or.inl hlabelmono) htr
    (annulusBoundarySource_mapsTo_closedStrip r x hr.ne' (hdR.trans hR1) upper)
    (fun _ hz => hsrc (hsub hz)) (hH.mono hsub) (fun z hz => hmetric z (hsub hz))
    (fun _ hz => halfDiskGradient_restrict hd hdR.le hH hz) hV (fun z hz => (hunit z hz).1)
  have hboundary' : ∀ᶠ t : ℝ in 𝓝 0,
      ContDiffAt ℝ 1 (fun s : ℝ => (V (s : ℂ)).1) t ∧
      gE.inner (H (t : ℂ))
        (deriv (fun s : ℝ => (V (s : ℂ)).1) t +
          connectionCoefficient DE (H (t : ℂ))
            (fderivWithin ℝ H K (t : ℂ) 1) (V (t : ℂ)).1) (V (t : ℂ)).2 =
        (if upper then -1 else 1) * B (x + r * t) := by
    filter_upwards [hboundary] with t ht
    refine ⟨ht.1, ht.2.trans ?_⟩
    change g.inner (A.map (P (t : ℂ))) (kappa (label t))
      (mfderivWithin (𝓡 2) (𝓡 n) A.map S (P (t : ℂ))
        (annulusBoundaryLinear r hr.ne' upper I)) = _
    rw [annulusBoundaryLinear_I]
    have hPt := annulusBoundarySource_real r hr.ne' upper x t
    change P (t : ℂ) = _ at hPt
    rw [hPt]
    cases upper <;> simp only [B, label,
      Bool.false_eq_true, if_false, if_true, map_neg, one_mul, neg_one_mul]
  obtain ⟨eta, heta, hetasub⟩ := nhds_basis_closedBall.mem_iff.mp hboundary'
  let e := min (d / 4) (eta / 2)
  have he : 0 < e := lt_min (by positivity) (half_pos heta)
  have heD : 2 * e < d := by
    have hh := min_le_left (d / 4) (eta / 2)
    dsimp only [e]
    linarith
  refine ⟨gE, DE, d, e, C, V, hd, hdR.trans hR1, he, heD, hC,
    hH.mono hsub, hV, hVi, hDF, hholder, ?_, ?_⟩
  · intro z hz
    exact (annulus_chart_connection_log A hr x upper hAi gE DE hR1 hsrc hHi hmetric hconf z
      ⟨ball_subset_ball hdR.le hz.1, hz.2⟩ (hunit z
        ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩).1).2
  · intro t ht
    apply hetasub
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans ((min_le_right _ _).trans (by linarith))

end PoincareConjecture.M64
