import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ScalarInterpolationCollar












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64_zero_area_boundary_collar_reverse
    (g : RiemannianMetric n M) (c : ℝ → M) (sigma : ℝ → ℝ)
    (hc : Continuous c)
    (hc_periodic : ∀ x : ℝ, c (x + curvePeriod) = c x)
    (hc_lipschitz : ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ x y : ℝ,
      g.edist (c x) (c y) ≤ ENNReal.ofReal Lc * ENNReal.ofReal |x - y|)
    (hsigma : Continuous sigma)
    (hsigma_periodic : ∀ x : ℝ, sigma (x + curvePeriod) = sigma x + curvePeriod)
    (hsigma_lipschitz : ∃ Ls : ℝ, 0 ≤ Ls ∧ ∀ x y : ℝ,
      |sigma x - sigma y| ≤ Ls * |x - y|) :
    ∃ A : M64Annulus g (c ∘ sigma) c,
      A.map = (fun p : LoopPlane =>
        c ((1 - p 1) * sigma (p 0) + p 1 * p 0)) ∧ A.area = 0 := by
  obtain ⟨A, hAmap, hAarea⟩ := m64_zero_area_boundary_collar g c sigma hc
    hc_periodic hc_lipschitz hsigma hsigma_periodic hsigma_lipschitz
  let R : LoopPlane → LoopPlane := m64RadialAffine (-1) 1
  let F : LoopPlane → M := A.map ∘ R
  have hRmem : ∀ p ∈ m64AnnulusDomain, R p ∈ m64AnnulusDomain := by
    intro p hp
    change 0 ≤ (R p) 0 ∧ (R p) 0 ≤ curvePeriod ∧
      0 ≤ (R p) 1 ∧ (R p) 1 ≤ 1
    simp only [R, m64RadialAffine, annulusPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · exact hp.1
    constructor
    · exact hp.2.1
    constructor <;> linarith [hp.2.2.1, hp.2.2.2]
  have hRinvol : Function.Involutive R := by
    intro p
    ext i
    fin_cases i <;> simp [R, m64RadialAffine, annulusPoint]
  have hRannulus (x s : ℝ) :
      R (annulusPoint x s) = annulusPoint x (1 - s) := by
    ext i
    fin_cases i <;> simp [R, m64RadialAffine, annulusPoint]
    ring
  have hRimage : R '' m64AnnulusDomain = m64AnnulusDomain := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hRmem q hq
    · intro hp
      refine ⟨R p, hRmem p hp, ?_⟩
      exact hRinvol p
  have hRnorm (p q : LoopPlane) : ‖R p - R q‖ = ‖p - q‖ := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    fin_cases i <;>
      simp [R, m64RadialAffine, annulusPoint, PiLp.sub_apply, Real.norm_eq_abs]
    ring
  have hRcont : Continuous R := by
    unfold R m64RadialAffine annulusPoint
    fun_prop
  have hFcont : ContinuousOn F m64AnnulusDomain := by
    simpa only [F] using A.continuous_on_domain.comp hRcont.continuousOn hRmem
  have hFperiodic : ∀ x s : ℝ,
      F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s) := by
    intro x s
    change A.map (R (annulusPoint (x + curvePeriod) s)) =
      A.map (R (annulusPoint x s))
    rw [hRannulus, hRannulus]
    exact A.periodic x (1 - s)
  have hFlower : ∀ x : ℝ, F (annulusPoint x 0) = (c ∘ sigma) x := by
    intro x
    rw [show F (annulusPoint x 0) = A.map (annulusPoint x 1) by
      simp only [F, Function.comp_apply, hRannulus]
      norm_num]
    exact A.upper_boundary x
  have hFupper : ∀ x : ℝ, F (annulusPoint x 1) = c x := by
    intro x
    rw [show F (annulusPoint x 1) = A.map (annulusPoint x 0) by
      simp only [F, Function.comp_apply, hRannulus]
      norm_num]
    exact A.lower_boundary x
  have hFLip : ∀ x y : m64AnnulusDomain,
      g.edist (F x) (F y) ≤
        ENNReal.ofReal A.lipschitz_constant *
          ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    calc
      g.edist (F x) (F y) ≤ ENNReal.ofReal A.lipschitz_constant *
          ENNReal.ofReal ‖R (x : LoopPlane) - R (y : LoopPlane)‖ := by
        simpa only [F, Function.comp_apply] using
          A.lipschitz_on_domain ⟨R x, hRmem x x.2⟩ ⟨R y, hRmem y y.2⟩
      _ = ENNReal.ofReal A.lipschitz_constant *
          ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by rw [hRnorm]
  have hareaF : (∫ z in m64AnnulusDomain, m60AreaDensity g F z) = 0 := by
    have hcomp := m64AreaIntegral_comp_radialAffine g A.map
      (by norm_num : (-1 : ℝ) ≠ 0) 1 m64AnnulusDomain_measurableSet
    rw [show F = A.map ∘ R by rfl, hcomp, hRimage]
    simpa only [M64Annulus.area, m64AnnulusArea] using hAarea
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨B, hBmap, _⟩ := m64Annulus_of_lipschitz g F hFcont hFperiodic
    hFlower hFupper A.lipschitz_nonnegative hFLip hfinite
    (show (∫ z in m64AnnulusDomain, m60AreaDensity g F z) < 1 by
      rw [hareaF]
      norm_num)
  refine ⟨B, ?_, ?_⟩
  · rw [hBmap]
    funext p
    change A.map (R p) = _
    rw [hAmap]
    simp only [R, m64RadialAffine, annulusPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    congr 1
    ring_nf
  · change (∫ z in m64AnnulusDomain, m60AreaDensity g B.map z) = 0
    rw [hBmap]
    exact hareaF

end PoincareConjecture
