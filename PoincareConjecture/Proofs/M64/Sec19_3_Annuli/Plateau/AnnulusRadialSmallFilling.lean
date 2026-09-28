import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialUniformFilling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialBoundaryRadius
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialPhaseFixed













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1
local notation "K" => closedBall (0 : LoopPlane) 1
local notation "mu" => volume.restrict S
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




theorem m64ChartReadable_small_radial_H1_filling
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
    (hcP : Function.Periodic c curvePeriod) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ rho : ℝ, 0 < rho ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : LoopPlane) (r : ℝ), 0 < r → r ≤ rho →
        ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
          (∀ t, angularPoint t 1 ≤ 0 → gamma t = c ((a + r • angularPoint t) 0)) →
          ∀ (w : ℕ → ℝ → E), (∀ j, ContDiff ℝ 1 (w j)) →
            (∀ j, Function.Periodic (w j) curvePeriod) →
            TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
            ∀ v : ℝ → E, MemLp v 2 circleMu →
              (∀ x ∈ Icc (0 : ℝ) curvePeriod,
                e (gamma x) - e (gamma 0) = ∫ t in (0 : ℝ)..x, v t) →
              Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
                ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
              (∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) < epsilon →
              ∃ (F : LoopPlane → M) (W : Fin 2 → Lp E 2 mu),
                ContinuousOn F K ∧ (∀ t, F (angularPoint t) = gamma t) ∧
                (∀ z ∈ K, z 1 ≤ 0 → F z = c ((a + r • z) 0)) ∧
                MemLp (e ∘ F) 2 mu ∧
                (∀ i, ∀ᵐ z ∂mu, W i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F z))) ∧
                (∀ i b, HasWeakPartialDeriv i
                  (fun z => W i z b) (fun z => e (F z) b) S) ∧
                ∀ i, ‖W i‖ ^ 2 ≤ C *
                  ((∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2) + r ^ 2) := by
  obtain ⟨delta, hdelta, C0, hC0, hfill⟩ :=
    m64ChartReadable_uniform_radial_H1_filling_radius g e he hei hread
  have hce : ContDiff ℝ 1 (e ∘ c) := contMDiff_iff_contDiff.mp (he.comp hc)
  have hceP : Function.Periodic (e ∘ c) curvePeriod := fun x => congrArg e (hcP x)
  obtain ⟨D, hD, hrad⟩ := m64RadialBoundaryPlane_radius hce hceP
  obtain ⟨B, hB, henergy⟩ := m64RadialBoundaryPlane_energy_bound hce hceP
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let rho := delta / (D + 1)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  refine ⟨delta ^ 2 / curvePeriod, by positivity, rho, hrho, C0 * (B + 1),
    mul_nonneg hC0 (by positivity), ?_⟩
  intro a r hr hrrho gamma hgamma hgammaP hmatch w hw hwP hlim v hv hFTC hder hsmall
  have hgammaSmall (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      dist (e (gamma x)) (e (gamma 0)) < delta := by
    have hrad := m64H1Trace_radius_sq_le (e ∘ gamma) v hv hFTC hx
    have hE := (lt_div_iff₀ hP).mp hsmall
    rw [dist_eq_norm]
    change ‖e (gamma x) - e (gamma 0)‖ ^ 2 ≤
      curvePeriod * ∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2 at hrad
    nlinarith [norm_nonneg (e (gamma x) - e (gamma 0))]
  have hzero : gamma 0 = c (a 0 + r) := by
    simpa only [angularPoint, Real.cos_zero, Real.sin_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_one] using
      hmatch 0 (by simp [angularPoint])
  have hbSmall (z : LoopPlane) (hz : z ∈ K) :
      dist (e (c ((a + r • z) 0))) (e (gamma 0)) < delta := by
    rw [hzero]
    have hle := hrad a r hr.le z hz
    have hprod : rho * (D + 1) = delta := by
      exact div_mul_cancel₀ delta (by positivity : D + 1 ≠ 0)
    have hrbound := mul_le_mul_of_nonneg_left hrrho hD
    change dist (e (c ((a + r • z) 0))) (e (c (a 0 + r))) ≤ D * r at hle
    nlinarith
  obtain ⟨F, W, hFc, hcircle, hfixed, hu, ht, hweak, hbound⟩ :=
    hfill gamma hgamma hgammaP hgammaSmall (fun z => c ((a + r • z) 0))
      (m64RadialBoundaryPlane_contMDiff hc a r) hbSmall
      (m64RadialBoundaryPlane_reflection c a r) hmatch w hw hwP hlim v hv hder
  refine ⟨F, W, hFc, hcircle, hfixed, hu, ht, hweak, ?_⟩
  intro i
  apply (hbound i).trans
  have hb := henergy a r
  simp only [Function.comp_def] at hb
  have hE : 0 ≤ ∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC0
  change (∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2) +
    (∫ z in S, ‖fderiv ℝ (fun y : LoopPlane => e (c ((a + r • y) 0))) z
      (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2) +
    (∫ z in S, ‖fderiv ℝ (fun y : LoopPlane => e (c ((a + r • y) 0))) z
      (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2) ≤ _
  nlinarith [mul_nonneg hB hE, sq_nonneg r]

end PoincareConjecture
