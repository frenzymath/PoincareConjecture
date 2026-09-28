import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseGreenAdmission
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LiftNormalization
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.OriginalCircleObservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_freeWeakPhase_seed
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    (c0 c1 : ℝ → Q.charts.Point) (H0 H1 : ℝ ≃o ℝ)
    (hzero : ∀ x, P.circle.quotient (H0 x) = (c0 x).1.2)
    (hone : ∀ x, P.circle.quotient (H1 x) = (c1 x).1.2)
    {D : ℝ} (hdegree : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (hnorm0 : sigma0.map 0 ∈ Icc (0 : ℝ) curvePeriod)
    (hnorm1 : sigma1.map 0 ∈ Icc (0 : ℝ) curvePeriod)
    (A : M64Annulus (Q.flow.metric time) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map S) :
    ∃ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) D,
      W.label0 = sigma0.map ∧ W.label1 = sigma1.map ∧ W.annulus.map = A.map ∧
      (∀ i, ∀ᵐ p ∂mu, W.annulus.column i p =
        fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) ∧
      ∃ k : ℤ, W.offset = k * circumference := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let := Q.charts.chartedSpace
  obtain ⟨-, B, hBmap, -, -, -⟩ := m64ProjectedAnnulus_of_annulus Q time
    (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) A
  have hfst : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 (n + 1)) 1
      (Prod.fst : Q.charts.Point → P.charts.Point) :=
    (contMDiff_fst.comp Q.charts.to_product_smooth).of_le (by simp)
  have hB : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 B.map S := by
    rw [hBmap]
    exact hfst.comp_contMDiffOn hA
  have hcont (sigma : M64PeriodicDegreeOneLift) : Continuous sigma.map := by
    have hLip : LipschitzWith ⟨sigma.lipschitz_constant, sigma.lipschitz_nonnegative⟩
        sigma.map := LipschitzWith.of_dist_le_mul (fun x y => by
      change |sigma.map x - sigma.map y| ≤ sigma.lipschitz_constant * |x - y|
      exact sigma.lipschitz_on x y)
    exact hLip.continuous
  obtain ⟨L, k, -, -, hL2, hcol, hquot, -, -, -, hvertical, hhorizontal⟩ :=
    annulus_exists_real_weak_phase P time B hB (H0 ∘ sigma0.map) (H1 ∘ sigma1.map)
      (H0.continuous.comp (hcont sigma0)) (H1.continuous.comp (hcont sigma1))
      (fun x _ => hzero (sigma0.map x)) (fun x _ => hone (sigma1.map x)) (by
        change H0 (sigma0.map curvePeriod) = H0 (sigma0.map 0) + D
        have hp := sigma0.period_shift 0
        rw [zero_add] at hp
        rw [hp, hdegree])
  obtain ⟨V, hVmap, hVcol⟩ := m64ObservedWeakAnnulus_of_annulus A e he
  let u : Lp ℝ 2 mu := hL2.toLp L
  let v : Fin 2 → Lp ℝ 2 mu := fun i =>
    (hcol i).1.toLp (fun p => fderiv ℝ L p (EuclideanSpace.single i 1))
  have hu : u =ᵐ[mu] L := hL2.coeFn_toLp
  have hv (i : Fin 2) : v i =ᵐ[mu]
      (fun p => fderiv ℝ L p (EuclideanSpace.single i 1)) := (hcol i).1.coeFn_toLp
  have hobs (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      R (e (A.map p)) = angularPoint (curvePeriod / circumference * L p) := by
    have hq : P.circle.quotient (L p) = (A.map p).1.2 := by
      simpa only [hBmap] using hquot p hp
    rw [hR, ← hq, planarCircleObservation_quotient]
  have htest (i : Fin 2) (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p * v i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
      (∫ p in S, phi p * fderiv ℝ L p (EuclideanSpace.single i 1)) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * L p) := by
    congr 1
    · exact integral_congr_ae ((hv i).mono fun p hp => congrArg (phi p * ·) hp)
    · exact integral_congr_ae (hu.mono fun p hp =>
        congrArg (fderiv ℝ phi p (EuclideanSpace.single i 1) * ·) hp)
  let W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) D := {
    label0 := sigma0.map
    label1 := sigma1.map
    label0_monotone := sigma0.monotone
    label1_monotone := sigma1.monotone
    label0_period := sigma0.period_shift
    label1_period := sigma1.period_shift
    label0_normalized := hnorm0
    label1_normalized := hnorm1
    annulus := V
    phase := u
    phaseColumn := v
    phase_weak := fun i => m64WeakPartialDeriv_ae_congr hu.symm (hv i).symm (hcol i).2
    phase_observation := by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet, hu] with p hp hup
      rw [hVmap, hobs p (interior_subset hp), hup]
    offset := k * circumference
    offset_circle := by
      have hz : P.circle.quotient ((k : ℝ) * circumference) = P.circle.quotient 0 := by
        apply (AddCircle.coe_eq_zero_iff circumference).mpr
        exact ⟨k, by simp only [zsmul_eq_mul]⟩
      rw [← planarCircleObservation_quotient P.circle, hz, planarCircleObservation_quotient]
      simp only [mul_zero]
    phase_boundary := fun phi hphi => (htest 1 phi).trans (hvertical phi hphi)
    phase_seam := by
      intro phi hphi hperiod
      rw [htest, hhorizontal phi hphi hperiod]
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact (hperiod s hs).symm }
  exact ⟨W, rfl, rfl, hVmap, hVcol, k, rfl⟩

end PoincareConjecture.M64
