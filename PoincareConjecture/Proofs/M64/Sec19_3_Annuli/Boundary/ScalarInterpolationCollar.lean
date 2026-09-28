import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ScalarFactorArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.AnnulusJoinArea















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

local notation "S" => m64AnnulusInterior





theorem m64_zero_area_boundary_collar
    (g : RiemannianMetric n M) (c : ℝ → M) (sigma : ℝ → ℝ)
    (hc : Continuous c)
    (hc_periodic : ∀ x : ℝ, c (x + curvePeriod) = c x)
    (hc_lipschitz : ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ x y : ℝ,
      g.edist (c x) (c y) ≤ ENNReal.ofReal Lc * ENNReal.ofReal |x - y|)
    (hsigma : Continuous sigma)
    (hsigma_periodic : ∀ x : ℝ, sigma (x + curvePeriod) = sigma x + curvePeriod)
    (hsigma_lipschitz : ∃ Ls : ℝ, 0 ≤ Ls ∧ ∀ x y : ℝ,
      |sigma x - sigma y| ≤ Ls * |x - y|) :
    ∃ A : M64Annulus g c (c ∘ sigma),
      A.map = (fun p : LoopPlane =>
        c ((1 - p 1) * p 0 + p 1 * sigma (p 0))) ∧ A.area = 0 := by
  obtain ⟨Lc, hLc, hcL⟩ := hc_lipschitz
  obtain ⟨Ls, hLs, hsL⟩ := hsigma_lipschitz
  let ell : LoopPlane → ℝ := fun p =>
    (1 - p 1) * p 0 + p 1 * sigma (p 0)
  let F : LoopPlane → M := c ∘ ell
  let K : ℝ := 1 + Ls + curvePeriod + |sigma 0| + Ls * curvePeriod
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let K0 : ℝ≥0 := ⟨K, hK⟩
  let Lc0 : ℝ≥0 := ⟨Lc, hLc⟩
  have hSsub : S ⊆ m64AnnulusDomain := by
    intro x hx
    simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, Set.mem_Ioo] at hx
    change 0 ≤ x 0 ∧ x 0 ≤ curvePeriod ∧ 0 ≤ x 1 ∧ x 1 ≤ 1
    have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    exact ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩
  have hcoords {p : LoopPlane} (hp : p ∈ m64AnnulusDomain) :
      0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := hp
  have hscalar_bound {p q : LoopPlane}
      (hp : p ∈ m64AnnulusDomain) (hq : q ∈ m64AnnulusDomain) :
      |ell p - ell q| ≤ K * ‖p - q‖ := by
    have hp' := hcoords hp
    have hq' := hcoords hq
    have hxp : |p 0 - q 0| ≤ ‖p - q‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) 0
    have hsp : |p 1 - q 1| ≤ ‖p - q‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) 1
    have hsigma_q : |sigma (q 0)| ≤ |sigma 0| + Ls * curvePeriod := by
      calc
        |sigma (q 0)| ≤ |sigma (q 0) - sigma 0| + |sigma 0| := by
          calc
            |sigma (q 0)| = |(sigma (q 0) - sigma 0) + sigma 0| := by ring_nf
            _ ≤ |sigma (q 0) - sigma 0| + |sigma 0| := abs_add_le _ _
        _ ≤ Ls * |q 0 - 0| + |sigma 0| := by
          gcongr
          exact hsL (q 0) 0
        _ ≤ Ls * curvePeriod + |sigma 0| := by
          have hq0 : |q 0 - 0| ≤ curvePeriod := by
            rw [sub_zero, abs_of_nonneg hq'.1]
            exact hq'.2.1
          have hmul := mul_le_mul_of_nonneg_left hq0 hLs
          exact add_le_add hmul (le_refl _)
        _ = |sigma 0| + Ls * curvePeriod := by ring
    have hterm0 :
        |(1 - p 1) * (p 0 - q 0)| ≤ ‖p - q‖ := by
      rw [abs_mul, abs_of_nonneg (by linarith [hp'.2.2.2])]
      calc
        (1 - p 1) * |p 0 - q 0| ≤ 1 * |p 0 - q 0| :=
          by
            simpa only [one_mul] using
              (mul_le_of_le_one_left (abs_nonneg (p 0 - q 0))
                (sub_le_self _ hp'.2.2.1))
        _ ≤ ‖p - q‖ := by simpa only [one_mul] using hxp
    have hterm1 :
        |p 1 * (sigma (p 0) - sigma (q 0))| ≤ Ls * ‖p - q‖ := by
      rw [abs_mul]
      have hsig := hsL (p 0) (q 0)
      have hp1 : |p 1| ≤ 1 := by simpa [abs_of_nonneg hp'.2.2.1] using hp'.2.2.2
      calc
        |p 1| * |sigma (p 0) - sigma (q 0)| ≤
            1 * (Ls * |p 0 - q 0|) := by gcongr
        _ ≤ Ls * ‖p - q‖ := by simpa using (mul_le_mul_of_nonneg_left hxp hLs)
    have hterm2 :
        |(q 1 - p 1) * q 0| ≤ curvePeriod * ‖p - q‖ := by
      rw [abs_mul]
      have hq0 : |q 0| ≤ curvePeriod := by simpa [abs_of_nonneg hq'.1] using hq'.2.1
      calc
        |q 1 - p 1| * |q 0| ≤ ‖p - q‖ * curvePeriod :=
          mul_le_mul (by simpa only [abs_sub_comm] using hsp) hq0
            (abs_nonneg _) (by positivity)
        _ = curvePeriod * ‖p - q‖ := by ring
    have hterm3 :
        |(p 1 - q 1) * sigma (q 0)| ≤
          (|sigma 0| + Ls * curvePeriod) * ‖p - q‖ := by
      rw [abs_mul]
      calc
        |p 1 - q 1| * |sigma (q 0)| ≤
            ‖p - q‖ * (|sigma 0| + Ls * curvePeriod) :=
          mul_le_mul hsp hsigma_q (abs_nonneg _) (by positivity)
        _ = (|sigma 0| + Ls * curvePeriod) * ‖p - q‖ := by ring
    have hdecomp : ell p - ell q =
        (1 - p 1) * (p 0 - q 0) +
          p 1 * (sigma (p 0) - sigma (q 0)) +
          (q 1 - p 1) * q 0 + (p 1 - q 1) * sigma (q 0) := by
      dsimp [ell]
      ring
    rw [hdecomp]
    calc
      |(1 - p 1) * (p 0 - q 0) + p 1 * (sigma (p 0) - sigma (q 0)) +
          (q 1 - p 1) * q 0 + (p 1 - q 1) * sigma (q 0)| ≤
          |(1 - p 1) * (p 0 - q 0)| +
            |p 1 * (sigma (p 0) - sigma (q 0))| +
            |(q 1 - p 1) * q 0| + |(p 1 - q 1) * sigma (q 0)| := by
        calc
          _ ≤ |(1 - p 1) * (p 0 - q 0) + p 1 * (sigma (p 0) - sigma (q 0)) +
              (q 1 - p 1) * q 0| + |(p 1 - q 1) * sigma (q 0)| := abs_add_le _ _
          _ ≤ (|(1 - p 1) * (p 0 - q 0)| +
              |p 1 * (sigma (p 0) - sigma (q 0))| +
              |(q 1 - p 1) * q 0|) + |(p 1 - q 1) * sigma (q 0)| := by
            have hsum3 :
                |(1 - p 1) * (p 0 - q 0) +
                  p 1 * (sigma (p 0) - sigma (q 0)) +
                  (q 1 - p 1) * q 0| ≤
                |(1 - p 1) * (p 0 - q 0)| +
                  |p 1 * (sigma (p 0) - sigma (q 0))| +
                  |(q 1 - p 1) * q 0| := by
              calc
                _ ≤ |(1 - p 1) * (p 0 - q 0) +
                    p 1 * (sigma (p 0) - sigma (q 0))| +
                    |(q 1 - p 1) * q 0| := abs_add_le _ _
                _ ≤ (|(1 - p 1) * (p 0 - q 0)| +
                    |p 1 * (sigma (p 0) - sigma (q 0))|) +
                    |(q 1 - p 1) * q 0| :=
                  add_le_add (abs_add_le _ _) (le_refl _)
                _ = _ := by ring
            exact add_le_add hsum3 (le_refl _)
          _ = _ := by ring
      _ ≤ K * ‖p - q‖ := by
        dsimp [K]
        nlinarith [hterm0, hterm1, hterm2, hterm3]
  have hscalar_lip : LipschitzOnWith K0 ell S := by
    intro p hp q hq
    have hpD : p ∈ m64AnnulusDomain := by
      exact hSsub hp
    have hqD : q ∈ m64AnnulusDomain := by
      exact hSsub hq
    have h := hscalar_bound hpD hqD
    change edist (ell p) (ell q) ≤
      (K0 : ℝ≥0∞) * edist p q
    have h' : ENNReal.ofReal |ell p - ell q| ≤
        ENNReal.ofReal K * ENNReal.ofReal ‖p - q‖ := by
      rw [← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal h
    have hK0 : (K0 : ℝ≥0∞) = ENNReal.ofReal K := by
      change ENNReal.ofNNReal (NNReal.mk K hK) = ENNReal.ofReal K
      rw [ENNReal.ofReal_eq_coe_nnreal hK]
    rw [hK0]
    simpa only [edist_dist, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h'
  have hscalar_factor : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (F x) (F y) ≤
        (Lc0 : ℝ≥0∞) * ENNReal.ofReal |ell x - ell y| := by
    intro x hx y hy
    have h := hcL (ell x) (ell y)
    have hLc0 : (Lc0 : ℝ≥0∞) = ENNReal.ofReal Lc := by
      change ENNReal.ofNNReal (NNReal.mk Lc hLc) = ENNReal.ofReal Lc
      rw [ENNReal.ofReal_eq_coe_nnreal hLc]
    rw [hLc0]
    simpa only [F, Function.comp_apply] using h
  obtain ⟨hzero, _hint, hzero_int⟩ :=
    m60AreaIntegral_eq_zero_of_scalar_increment_bound g isOpen_m64AnnulusInterior
      hscalar_lip hscalar_factor
  have hzero_global : ∀ᵐ z ∂volume, z ∈ S → m60AreaDensity g F z = 0 :=
    (ae_restrict_iff' isOpen_m64AnnulusInterior.measurableSet).mp hzero
  have hzero_domain : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      m60AreaDensity g F z = 0 := by
    apply (ae_restrict_iff' m64AnnulusDomain_measurableSet).mpr
    filter_upwards [hzero_global, m64AnnulusDomain_ae_eq_interior] with z hz hzS hzD
    exact hz (hzS.mp hzD)
  have harea_zero : (∫ z in m64AnnulusDomain, m60AreaDensity g F z) = 0 := by
    rw [integral_congr_ae hzero_domain, integral_zero]
  have hFcont : ContinuousOn F m64AnnulusDomain := by
    apply (hc.comp (by fun_prop)).continuousOn
  have hFperiodic : ∀ x s : ℝ,
      F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s) := by
    intro x s
    have hell_period : ell (annulusPoint (x + curvePeriod) s) =
        ell (annulusPoint x s) + curvePeriod := by
      dsimp [ell, annulusPoint]
      rw [hsigma_periodic x]
      ring
    change c (ell (annulusPoint (x + curvePeriod) s)) =
      c (ell (annulusPoint x s))
    rw [hell_period, hc_periodic]
  have hFlower : ∀ x : ℝ, F (annulusPoint x 0) = c x := by
    intro x
    dsimp [F, ell, Function.comp_def, annulusPoint]
    simp
  have hFupper : ∀ x : ℝ, F (annulusPoint x 1) = (c ∘ sigma) x := by
    intro x
    dsimp [F, ell, Function.comp_def, annulusPoint]
    simp
  have hFell : ∀ p q : m64AnnulusDomain,
      g.edist (F p) (F q) ≤
        ENNReal.ofReal (Lc * K) * ENNReal.ofReal ‖(p : LoopPlane) - q‖ := by
    intro p q
    have hcurve := hcL (ell p) (ell q)
    have hell := hscalar_bound p.2 q.2
    have hmul := ENNReal.ofReal_le_ofReal hell
    have hnonneg : 0 ≤ K * ‖(p : LoopPlane) - q‖ := mul_nonneg hK (norm_nonneg _)
    calc
      g.edist (F p) (F q) ≤ ENNReal.ofReal Lc * ENNReal.ofReal |ell p - ell q| := by
        simpa only [F, Function.comp_apply] using hcurve
      _ ≤ ENNReal.ofReal Lc * ENNReal.ofReal (K * ‖(p : LoopPlane) - q‖) := by
        gcongr
      _ = ENNReal.ofReal (Lc * K) * ENNReal.ofReal ‖(p : LoopPlane) - q‖ := by
        rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hLc]
        ring
  have hfinite : volume S ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨A, hmap, harea⟩ := m64Annulus_of_lipschitz g F hFcont hFperiodic
    hFlower hFupper (mul_nonneg hLc hK) hFell hfinite
    (show (∫ z in m64AnnulusDomain, m60AreaDensity g F z) < 1 by
      rw [harea_zero]
      norm_num)
  refine ⟨A, hmap, ?_⟩
  change (∫ z in m64AnnulusDomain, m60AreaDensity g A.map z) = 0
  rw [hmap]
  exact harea_zero





theorem m64_zero_area_boundary_collar_join
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (c : ℝ → M) (sigma : ℝ → ℝ) (hAupper : c1 = c)
    (hc : Continuous c)
    (hc_periodic : ∀ x : ℝ, c (x + curvePeriod) = c x)
    (hc_lipschitz : ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ x y : ℝ,
      g.edist (c x) (c y) ≤ ENNReal.ofReal Lc * ENNReal.ofReal |x - y|)
    (hsigma : Continuous sigma)
    (hsigma_periodic : ∀ x : ℝ, sigma (x + curvePeriod) = sigma x + curvePeriod)
    (hsigma_lipschitz : ∃ Ls : ℝ, 0 ≤ Ls ∧ ∀ x y : ℝ,
      |sigma x - sigma y| ≤ Ls * |x - y|) :
    ∃ C : M64Annulus g c0 (c ∘ sigma),
      C.area = A.area := by
  subst c1
  obtain ⟨B, hBmap, hBarea⟩ := m64_zero_area_boundary_collar g c sigma hc
    hc_periodic hc_lipschitz hsigma hsigma_periodic hsigma_lipschitz
  obtain ⟨C, hCmap, hCarea⟩ := m64Annulus_join_with_area A B
  refine ⟨C, ?_⟩
  rw [hCarea, hBarea, add_zero]

end PoincareConjecture
