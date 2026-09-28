import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialAffineConeEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialObservedComposition
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialWeakLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeWeakFilling














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
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

set_option maxHeartbeats 1200000 in




theorem m64ChartReadable_local_radial_H1_filling
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (C : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        (∀ x, gamma x ∈ U) → ∀ b : LoopPlane → M,
          ContMDiff (𝓡 2) (𝓡 n) 1 b → (∀ z ∈ K, b z ∈ U) →
          (∀ z, b (m60PlaneReflection z) = b z) →
          (∀ t, (angularPoint t) 1 ≤ 0 → gamma t = b (angularPoint t)) →
          ∀ (w : ℕ → ℝ → E), (∀ j, ContDiff ℝ 1 (w j)) →
            (∀ j, Function.Periodic (w j) curvePeriod) →
            TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
            ∀ v : ℝ → E, MemLp v 2 circleMu →
              Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
                ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
              ∃ (F : LoopPlane → M) (W : Fin 2 → Lp E 2 mu),
                ContinuousOn F K ∧ (∀ t, F (angularPoint t) = gamma t) ∧
                (∀ z ∈ K, z 1 ≤ 0 → F z = b z) ∧ MemLp (e ∘ F) 2 mu ∧
                (∀ i, ∀ᵐ z ∂mu, W i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F z))) ∧
                (∀ i c, HasWeakPartialDeriv i
                  (fun z => W i z c) (fun z => e (F z) c) S) ∧
                ∀ i, ‖W i‖ ^ 2 ≤ C *
                  ((∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2) +
                    (∫ z in S, ‖fderiv ℝ (e ∘ b) z (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2) +
                    ∫ z in S, ‖fderiv ℝ (e ∘ b) z (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2) := by
  obtain ⟨U, R, B, T, hU, hp, hR, hB, hfix, hT, hbound⟩ :=
    m64ChartReadable_local_observed_correction g e he hread p
  obtain ⟨A, hA, hconeEnergy⟩ := m64EuclideanCone_energy_bound (m := m)
  let U' := U ∩ e ⁻¹' ball (e p) (R / 8)
  have hU' : IsOpen U' := hU.inter (isOpen_ball.preimage he.continuous)
  have hp' : p ∈ U' := ⟨hp, mem_ball_self (by positivity)⟩
  refine ⟨U', 12 * B ^ 2 * A + 3 * B ^ 2, hU', hp', by positivity, ?_⟩
  intro gamma hgamma hP hgammaU b hb hbU hbsym hmatch w hw hwP hlim v hv hder
  let h := e ∘ b
  have hh : ContDiff ℝ 1 h := contMDiff_iff_contDiff.mp (he.comp hb)
  have hshort (q : M) (hq : q ∈ U') : ‖e q - e p‖ < R / 8 := by
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using hq.2
  obtain ⟨k0, hk0⟩ := m64_periodic_approximation_eventually_in_ball w (e ∘ gamma) hwP
    hlim (e p) (by positivity : 0 < R / 4) (fun x _ => by
      simpa only [Function.comp_apply, dist_eq_norm, div_div,
        show (4 : ℝ) * 2 = 8 from by norm_num] using hshort _ (hgammaU x))
  let fj : ℕ → LoopPlane → E := fun j => m64EuclideanCone (w (j + k0))
  let f := m64EuclideanCone (e ∘ gamma)
  let Zj := fun j => m64RadialCorrect (fj j) h
  let Z := m64RadialCorrect f h
  let Fj := fun j => T ∘ Zj j
  let F := T ∘ Z
  have hf (j : ℕ) : ContDiff ℝ 1 (fj j) :=
    m64EuclideanCone_contDiff (hw _) (hwP _)
  have hfbound (j : ℕ) (z : LoopPlane) : ‖fj j z - e p‖ ≤ R / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using m64EuclideanCone_range
      (fun x => hk0 _ (Nat.le_add_left k0 j) x) z
  have hfb (z : LoopPlane) : ‖f z - e p‖ ≤ R / 4 := by
    apply (show f z ∈ closedBall (e p) (R / 4) from ?_)
    exact m64EuclideanCone_range (fun x => mem_closedBall.mpr
      ((hshort _ (hgammaU x)).le.trans (by linarith))) z
  have hhb (z : LoopPlane) (hz : z ∈ K) : ‖h z - e p‖ ≤ R / 4 :=
    (hshort _ (hbU z hz)).le.trans (by linarith)
  have hZjmap (j : ℕ) : MapsTo (Zj j) K (closedBall (e p) R) := by
    intro z hz
    exact mem_closedBall.mpr ((m64RadialCorrect_range_bound (by simp : (0 : LoopPlane) 1 = 0)
      (fun x _ => hfbound j x) hhb hz).trans (by linarith))
  have hZmap : MapsTo Z K (closedBall (e p) R) := by
    intro z hz
    exact mem_closedBall.mpr ((m64RadialCorrect_range_bound (by simp : (0 : LoopPlane) 1 = 0)
      (fun x _ => hfb x) hhb hz).trans (by linarith))
  have hfc : Continuous f := m64EuclideanCone_continuous (he.continuous.comp hgamma)
    (fun x => congrArg e (hP x))
  have hZc : Continuous Z := m64RadialCorrect_continuous hfc hh.continuous
  have hFc : ContinuousOn F K := fun z hz =>
    ((hT _ (hZmap hz)).continuousAt.comp hZc.continuousAt).continuousWithinAt
  have hwpoint (x : ℝ) : Tendsto (fun j => w (j + k0) x) atTop (𝓝 (e (gamma x))) :=
    ((m64Periodic_tendstoUniformly hwP (fun t => congrArg e (hP t)) hlim).tendsto_at x).comp
      (tendsto_add_atTop_nat k0)
  have hfpoint (z : LoopPlane) : Tendsto (fun j => fj j z) atTop (𝓝 (f z)) :=
    m64EuclideanCone_tendsto _ _ hwpoint z
  have hpoint (z : LoopPlane) (hz : z ∈ S) :
      Tendsto (fun j => Fj j z) atTop (𝓝 (F z)) :=
    (hT _ (hZmap (ball_subset_closedBall hz))).continuousAt.tendsto.comp
      (((hfpoint z).sub (hfpoint (m64RadialLowerFold z))).add_const (h z))
  have hZjLip (j : ℕ) : ∃ L, LipschitzOnWith L (Zj j) K := by
    obtain ⟨L, hL⟩ := (hf j).contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall (0 : LoopPlane) 1) (isCompact_closedBall (0 : LoopPlane) 1)
    obtain ⟨J, hJ⟩ := hh.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall (0 : LoopPlane) 1) (isCompact_closedBall (0 : LoopPlane) 1)
    exact ⟨_, m64RadialCorrect_lipschitzOn (by simp) hL hJ⟩
  choose L hL using hZjLip
  have hdata (j : ℕ) :=
    m64LipschitzDisk_observed_chart_composition e he T hB hT hbound (hL j) (hZjmap j)
  let V := fun j i z => fderiv ℝ (e ∘ Fj j) z (EuclideanSpace.single i 1)
  let E0 := ∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2
  let H := (∫ z in S, ‖fderiv ℝ h z (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2) +
    ∫ z in S, ‖fderiv ℝ h z (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2
  have hE0 : 0 ≤ E0 := integral_nonneg (fun _ => sq_nonneg _)
  have hH : 0 ≤ H := add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)
  have hHcol (i : Fin 2) : (∫ z in S, ‖fderiv ℝ h z (EuclideanSpace.single i 1)‖ ^ 2) ≤ H := by
    fin_cases i
    · exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)
    · exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)
  let bound := fun j => B ^ 2 * (12 * A *
    ((∫ t in Icc (0 : ℝ) curvePeriod, ‖deriv (w (j + k0)) t - v t‖ ^ 2) + E0) + 3 * H)
  have hboundlim : Tendsto bound atTop (𝓝 (B ^ 2 * (12 * A * E0 + 3 * H))) := by
    simpa only [bound, zero_add, Function.comp_def] using
      (((((hder.comp (tendsto_add_atTop_nat k0)).add_const E0).const_mul (12 * A)).add_const
        (3 * H)).const_mul (B ^ 2))
  have henergy (j : ℕ) (i : Fin 2) : (∫ z in S, ‖V j i z‖ ^ 2) ≤ bound j := by
    have hd : MemLp (deriv (w (j + k0))) 2 circleMu := by
      have hc := (hw (j + k0)).continuous_deriv (by simp)
      exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
        ((hc.norm.pow 2).integrableOn_Icc)
    have hcone := (hconeEnergy _ (hw (j + k0)) (hwP (j + k0)) i).trans
      (mul_le_mul_of_nonneg_left (m64_integral_norm_sq_le_twice_error hd hv) hA)
    have hc := m64RadialCorrect_column_energy_le (hf j) hh
      (by simp : (0 : LoopPlane) 1 = 0) 1 i
    apply ((hdata j).2.2.2.2.2 i).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
    dsimp only [bound, Zj, E0]
    nlinarith [hHcol i]
  obtain ⟨_, hFlp, _, W, _, _, _, htan, hweak, hnorm⟩ :=
    m64ObservedContinuousDisk_weak_limit e he hread 0 1 Fj F (fun j => (hdata j).1)
      hFc hpoint V (fun j => (hdata j).2.2.1) (fun j => (hdata j).2.2.2.2.1)
      (fun j => (hdata j).2.2.2.1) bound hboundlim henergy
  refine ⟨F, W, hFc, ?_, ?_, hFlp, htan, hweak, ?_⟩
  · have hsphere : EqOn Z f (sphere (0 : LoopPlane) 1) := by
      apply m64RadialCorrect_preserves_sphere (by simp)
      · intro z hz hzy
        have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
        have hang : angularPoint (m60PlaneAngle z) = z := by
          simpa only [hn, one_smul] using m60PlaneAngle_polar z
        rw [← hang]
        change m64EuclideanCone (e ∘ gamma) (angularPoint (m60PlaneAngle z)) = _
        rw [m64EuclideanCone_boundary (fun x => congrArg e (hP x))]
        exact congrArg e (hmatch _ (by simpa only [hang] using hzy))
      · intro z
        exact congrArg e (hbsym z)
    intro t
    have hz : angularPoint t ∈ sphere (0 : LoopPlane) 1 := by
      simp only [mem_sphere, dist_zero_right, norm_angularPoint]
    change T (Z (angularPoint t)) = gamma t
    rw [hsphere hz]
    change T (m64EuclideanCone (e ∘ gamma) (angularPoint t)) = _
    rw [m64EuclideanCone_boundary (fun x => congrArg e (hP x))]
    exact (hfix _ (hgammaU t).1).1
  · intro z hz hzy
    change T (m64RadialCorrect f h z) = b z
    rw [m64RadialCorrect_lower f h hzy]
    exact (hfix _ (hbU z hz).1).1
  · intro i
    apply (hnorm i).trans
    change B ^ 2 * (12 * A * E0 + 3 * H) ≤
      (12 * B ^ 2 * A + 3 * B ^ 2) * (E0 + _ + _)
    have hpos1 := mul_nonneg (mul_nonneg (sq_nonneg B) hA) hH
    have hpos2 := mul_nonneg (sq_nonneg B) hE0
    dsimp only [H] at *
    nlinarith

end PoincareConjecture
