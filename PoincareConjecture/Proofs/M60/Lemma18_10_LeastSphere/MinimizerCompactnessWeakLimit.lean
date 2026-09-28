import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessWeakVariation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

private theorem clm_tendsto_apply
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {L : ℕ → F →L[ℝ] H} {v : ℕ → F} {L0 : F →L[ℝ] H} {v0 : F}
    (hL : Tendsto L atTop (𝓝 L0)) (hv : Tendsto v atTop (𝓝 v0)) :
    Tendsto (fun j => L j (v j)) atTop (𝓝 (L0 v0)) :=
  isBoundedBilinearMap_apply.continuous.continuousAt.tendsto.comp (hL.prodMk_nhds hv)




theorem suVanishingPower_mul_tendsto
    {a b c : ℕ → ℝ} {a0 b0 : ℝ}
    (ha : Tendsto a atTop (𝓝 a0)) (hb : Tendsto b atTop (𝓝 b0))
    (hc : Tendsto c atTop (𝓝 0)) (hap : ∀ j, 0 < a j) (hcn : ∀ j, 0 ≤ c j)
    (hzero : a0 = 0 → b0 = 0) :
    Tendsto (fun j => (a j) ^ (c j) * b j) atTop (𝓝 b0) := by
  by_cases ha0 : a0 = 0
  · have hb0 := hzero ha0
    rw [hb0] at hb ⊢
    apply squeeze_zero_norm' ?_ (by simpa only [norm_zero] using hb.norm)
    have hsmall : ∀ᶠ j in atTop, a j < 1 :=
      ha.eventually (gt_mem_nhds (by simpa only [ha0] using zero_lt_one))
    filter_upwards [hsmall] with j hj
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (hap j).le _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one (hap j).le hj.le (hcn j))
  · simpa only [Real.rpow_zero, one_mul] using (ha.rpow hc (Or.inl ha0)).mul hb




theorem suVanishingPower_integral_tendsto
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (a b : ℕ → X → ℝ) (c : ℕ → ℝ) (a0 b0 : X → ℝ)
    {A B : ℝ} (hA : 1 ≤ A)
    (hc : Tendsto c atTop (𝓝 0)) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hm : ∀ j, AEStronglyMeasurable (fun x => (a j x) ^ (c j) * b j x) mu)
    (hbounds : ∀ j, ∀ᵐ x ∂mu, 0 < a j x ∧ a j x ≤ A ∧ ‖b j x‖ ≤ B)
    (hlim : ∀ᵐ x ∂mu,
      Tendsto (fun j => a j x) atTop (𝓝 (a0 x)) ∧
      Tendsto (fun j => b j x) atTop (𝓝 (b0 x)) ∧ (a0 x = 0 → b0 x = 0)) :
    Tendsto (fun j => ∫ x, (a j x) ^ (c j) * b j x ∂mu) atTop
      (𝓝 (∫ x, b0 x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => A * B) hm (integrable_const _)
  · intro j
    filter_upwards [hbounds j] with x hx
    have hp : (a j x) ^ (c j) ≤ A := by
      calc
        _ ≤ A ^ (c j) := Real.rpow_le_rpow hx.1.le hx.2.1 (hc0 j)
        _ ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (hc1 j)
        _ = A := Real.rpow_one _
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    exact mul_le_mul hp hx.2.2 (norm_nonneg _) (by linarith)
  · have hall : ∀ᵐ x ∂mu, ∀ j, 0 < a j x := by
      rw [ae_all_iff]
      exact fun j => (hbounds j).mono fun _ hx => hx.1
    filter_upwards [hlim, hall] with x hx hxpos
    exact suVanishingPower_mul_tendsto hx.1 hx.2.1 hc hxpos hc0 hx.2.2

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suCompactWeakLimitBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactWeakLimitBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactWeakLimitTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactWeakLimitTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem unweighted_variation_bound
    (g : RiemannianMetric n M) (b : M) (u phi : LoopPlane → E) (z : LoopPlane)
    {C D P : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hG : ‖g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (u z)‖ ≤ C)
    (hDG : ‖fderiv ℝ (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm) (u z)‖ ≤ C)
    (hu : ∀ i : Fin 2, ‖fderiv ℝ u z (e i)‖ ≤ D)
    (hphi : ‖phi z‖ ≤ P) (hdphi : ∀ i : Fin 2, ‖fderiv ℝ phi z (e i)‖ ≤ P) :
    ‖suWeightedChartVariation g b u (fun _ => 1) phi z‖ ≤
      2 * C * P * D ^ 2 + 4 * C * D * P := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let V := fun i : Fin 2 => fderiv ℝ u z (e i)
  have hfirst (i : Fin 2) :
      ‖fderiv ℝ G (u z) (phi z) (V i) (V i)‖ ≤ C * P * D ^ 2 := by
    calc
      _ ≤ ‖fderiv ℝ G (u z) (phi z)‖ * ‖V i‖ * ‖V i‖ :=
        (fderiv ℝ G (u z) (phi z)).le_opNorm₂ _ _
      _ ≤ (‖fderiv ℝ G (u z)‖ * ‖phi z‖) * ‖V i‖ * ‖V i‖ := by
        gcongr
        exact (fderiv ℝ G (u z)).le_opNorm _
      _ ≤ (C * P) * D * D := by
        gcongr
        · exact hu i
        · exact hu i
      _ = _ := by ring
  have hsecond (i : Fin 2) :
      ‖G (u z) (V i) (fderiv ℝ phi z (e i))‖ ≤ C * D * P := by
    calc
      _ ≤ ‖G (u z)‖ * ‖V i‖ * ‖fderiv ℝ phi z (e i)‖ := (G (u z)).le_opNorm₂ _ _
      _ ≤ C * D * P := by
        gcongr
        · exact hu i
        · exact hdphi i
  change ‖1 * ((∑ i : Fin 2, _) + 2 * ∑ i : Fin 2, _)‖ ≤ _
  rw [one_mul]
  calc
    _ ≤ ‖∑ i : Fin 2, fderiv ℝ G (u z) (phi z) (V i) (V i)‖ +
        2 * ‖∑ i : Fin 2, G (u z) (V i) (fderiv ℝ phi z (e i))‖ := by
      simpa only [norm_mul, Real.norm_ofNat] using norm_add_le
        (∑ i : Fin 2, fderiv ℝ G (u z) (phi z) (V i) (V i))
        (2 * ∑ i : Fin 2, G (u z) (V i) (fderiv ℝ phi z (e i)))
    _ ≤ (∑ _i : Fin 2, C * P * D ^ 2) + 2 * ∑ _i : Fin 2, C * D * P := by
      gcongr
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hfirst i)
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hsecond i)
    _ = _ := by simp only [Fin.sum_univ_two]; ring




theorem suWeightedChartVariation_tendsto
    (g : RiemannianMetric n M) (b : M)
    (u : ℕ → LoopPlane → E) (u0 phi : LoopPlane → E)
    (lambda : ℕ → LoopPlane → ℝ) (rho c : ℕ → ℝ) (z : LoopPlane)
    {lambda0 rho0 : ℝ}
    (htarget : u0 z ∈ (extChartAt (𝓡 n) b).target)
    (hu : Tendsto (fun j => u j z) atTop (𝓝 (u0 z)))
    (hdu : Tendsto (fun j => fderiv ℝ (u j) z) atTop (𝓝 (fderiv ℝ u0 z)))
    (hlambda : Tendsto (fun j => lambda j z) atTop (𝓝 lambda0))
    (hl0 : 0 < lambda0) (hl : ∀ j, 0 < lambda j z)
    (hrho : Tendsto rho atTop (𝓝 rho0)) (hr : ∀ j, 0 < rho j)
    (hc : Tendsto c atTop (𝓝 0)) (hc0 : ∀ j, 0 ≤ c j) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let w := fun j y => ((rho j) ^ 2 +
      (∑ i : Fin 2, G (u j y) (fderiv ℝ (u j) y (e i))
        (fderiv ℝ (u j) y (e i))) / lambda j y) ^ (c j)
    Tendsto (fun j => suWeightedChartVariation g b (u j) (w j) phi z) atTop
      (𝓝 (suAlphaChartVariation g b 1 u0
        (fun i y => fderiv ℝ u0 y (e i)) phi z)) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let V := fun j (i : Fin 2) => fderiv ℝ (u j) z (e i)
  let V0 := fun i : Fin 2 => fderiv ℝ u0 z (e i)
  let Q := fun j => ∑ i : Fin 2, G (u j z) (V j i) (V j i)
  let Q0 := ∑ i : Fin 2, G (u0 z) (V0 i) (V0 i)
  let T := fun j => (∑ i : Fin 2, fderiv ℝ G (u j z) (phi z) (V j i) (V j i)) +
    2 * ∑ i : Fin 2, G (u j z) (V j i) (fderiv ℝ phi z (e i))
  let T0 := (∑ i : Fin 2, fderiv ℝ G (u0 z) (phi z) (V0 i) (V0 i)) +
    2 * ∑ i : Fin 2, G (u0 z) (V0 i) (fderiv ℝ phi z (e i))
  have hG : ContDiffAt ℝ ∞ G (u0 z) := (g.contDiffOn_chartCoefficients b).contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds htarget)
  have hGt : Tendsto (fun j => G (u j z)) atTop (𝓝 (G (u0 z))) :=
    hG.continuousAt.tendsto.comp hu
  have hDGt : Tendsto (fun j => fderiv ℝ G (u j z)) atTop (𝓝 (fderiv ℝ G (u0 z))) :=
    (hG.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hu
  have hV (i : Fin 2) : Tendsto (fun j => V j i) atTop (𝓝 (V0 i)) :=
    clm_tendsto_apply hdu tendsto_const_nhds
  have hQ : Tendsto Q atTop (𝓝 Q0) :=
    tendsto_finsetSum _ (fun i _ => clm_tendsto_apply (clm_tendsto_apply hGt (hV i)) (hV i))
  have hT : Tendsto T atTop (𝓝 T0) :=
    (tendsto_finsetSum _ (fun i _ =>
      clm_tendsto_apply (clm_tendsto_apply
        (clm_tendsto_apply hDGt tendsto_const_nhds) (hV i)) (hV i))).add
        ((tendsto_finsetSum _ (fun i _ =>
          clm_tendsto_apply (clm_tendsto_apply hGt (hV i)) tendsto_const_nhds)).const_mul 2)
  have hGpos (y v : E) : 0 ≤ G y v v := by
    change 0 ≤ g.inner ((extChartAt (𝓡 n) b).symm y)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v)
    by_cases hv : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm y v = 0
    · rw [hv]
      simp
    · exact (g.pos _ _ hv).le
  have hQ0 : 0 ≤ Q0 := Finset.sum_nonneg fun i _ => hGpos _ _
  have hapos (j : ℕ) : 0 < (rho j) ^ 2 + Q j / lambda j z := by
    have hQj : 0 ≤ Q j := Finset.sum_nonneg fun i _ => hGpos _ _
    have := hr j
    have := div_nonneg hQj (hl j).le
    positivity
  have hzero : rho0 ^ 2 + Q0 / lambda0 = 0 → T0 = 0 := by
    intro hz
    have hQz : Q0 = 0 := by
      have hd : Q0 / lambda0 = 0 := by nlinarith [sq_nonneg rho0, div_nonneg hQ0 hl0.le]
      exact (div_eq_zero_iff).mp hd |>.resolve_right hl0.ne'
    obtain ⟨a, _, ha, _, _, _, hac⟩ := suAlpha_coordinate_metric_bounds g b isCompact_singleton
      (show {u0 z} ⊆ (extChartAt (𝓡 n) b).target from singleton_subset_iff.mpr htarget)
    have hVz (i : Fin 2) : V0 i = 0 := by
      have hle : G (u0 z) (V0 i) (V0 i) ≤ Q0 :=
        Finset.single_le_sum (fun k _ => hGpos _ _) (Finset.mem_univ i)
      have hnorm : ‖V0 i‖ ^ 2 = 0 := by
        have hh := hac (u0 z) (mem_singleton _) (V0 i)
        nlinarith [sq_nonneg ‖V0 i‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    simp only [T0, hVz, map_zero, zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
  have ht := suVanishingPower_mul_tendsto
    ((hrho.pow 2).add (hQ.div hlambda hl0.ne')) hT hc hapos hc0 hzero
  simpa only [suWeightedChartVariation, suAlphaChartVariation, sub_self, Real.rpow_zero,
    one_mul, G, V, V0, Q, T, T0, EuclideanSpace.basisFun_apply, Pi.div_apply] using! ht

open CoordinateExponential ConnectionVariation

set_option maxHeartbeats 1600000 in





theorem suWeightedEuler_limit_variation
    (g : RiemannianMetric n M) (b : M)
    (u : ℕ → LoopPlane → E) (u0 : LoopPlane → E)
    (lambda : ℕ → LoopPlane → ℝ) (lambda0 : LoopPlane → ℝ)
    (rho c : ℕ → ℝ) {rho0 C D R : ℝ} (center : LoopPlane)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Metric.ball center R))
    (hlambda : ∀ j, ContDiffOn ℝ ∞ (lambda j) (Metric.ball center R))
    (hrange : ∀ j, MapsTo (u j) (Metric.ball center R) (extChartAt (𝓡 n) b).target)
    (hrange0 : MapsTo u0 (Metric.ball center R) (extChartAt (𝓡 n) b).target)
    (hlim : ∀ z ∈ Metric.ball center R, Tendsto (fun j => u j z) atTop (𝓝 (u0 z)))
    (hdlim : ∀ z ∈ Metric.ball center R,
      Tendsto (fun j => fderiv ℝ (u j) z) atTop (𝓝 (fderiv ℝ u0 z)))
    (hllim : ∀ z ∈ Metric.ball center R,
      Tendsto (fun j => lambda j z) atTop (𝓝 (lambda0 z)))
    (hl0 : ∀ z ∈ Metric.ball center R, 0 < lambda0 z)
    (hl : ∀ j z, z ∈ Metric.ball center R → 0 < lambda j z)
    (hrho : Tendsto rho atTop (𝓝 rho0)) (hr : ∀ j, 0 < rho j)
    (hr1 : ∀ j, rho j ≤ 1) (hc : Tendsto c atTop (𝓝 0))
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hcoeff : ∀ j z, z ∈ Metric.ball center R →
      ‖g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (u j z)‖ ≤ C ∧
      ‖fderiv ℝ (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm) (u j z)‖ ≤ C)
    (hgrad : ∀ j z, z ∈ Metric.ball center R → ∀ i : Fin 2,
      ‖fderiv ℝ (u j) z (e i)‖ ≤ D)
    (hq : ∀ j z, z ∈ Metric.ball center R →
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      (∑ i : Fin 2, G (u j z) (fderiv ℝ (u j) z (e i))
        (fderiv ℝ (u j) z (e i))) / lambda j z ∈ Icc 0 1)
    (heq : ∀ j z, z ∈ Metric.ball center R →
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      let Gamma := christoffelBilinear G
      let w := fun y => ((rho j) ^ 2 + (∑ i : Fin 2,
        G (u j y) (fderiv ℝ (u j) y (e i)) (fderiv ℝ (u j) y (e i))) /
          lambda j y) ^ (c j)
      ∑ i : Fin 2, covDerivAlong Gamma (u j)
        (fun y => w y • fderiv ℝ (u j) y (e i)) (e i) z = 0)
    (phi : LoopPlane → E) (hphi : ContDiff ℝ ∞ phi) (hphic : HasCompactSupport phi)
    (hphis : tsupport phi ⊆ Metric.ball center R) :
    IntegrableOn (suAlphaChartVariation g b 1 u0
      (fun i y => fderiv ℝ u0 y (e i)) phi) (Metric.ball center R) ∧
    (∫ z in Metric.ball center R, suAlphaChartVariation g b 1 u0
      (fun i y => fderiv ℝ u0 y (e i)) phi z) = 0 := by
  let O := Metric.ball center R
  let mu := volume.restrict O
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let q := fun j y => (∑ i : Fin 2, G (u j y) (fderiv ℝ (u j) y (e i))
    (fderiv ℝ (u j) y (e i))) / lambda j y
  let w := fun j y => ((rho j) ^ 2 + q j y) ^ (c j)
  let F := fun j => suWeightedChartVariation g b (u j) (w j) phi
  let F0 := suAlphaChartVariation g b 1 u0 (fun i y => fderiv ℝ u0 y (e i)) phi
  have hw (j : ℕ) : ContDiffOn ℝ ∞ (w j) O := by
    intro z hz
    have huz := (hu j).contDiffAt (Metric.isOpen_ball.mem_nhds hz)
    have hGz := (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (hrange j hz))
    have hV (i : Fin 2) : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (u j) y (e i)) z :=
      (huz.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    have hQ := ContDiffAt.sum (s := Finset.univ)
      (fun i _ => (((hGz.comp z huz).clm_apply (hV i)).clm_apply (hV i)))
    have hqz := hQ.div ((hlambda j).contDiffAt (Metric.isOpen_ball.mem_nhds hz)) (hl j z hz).ne'
    have hpos : 0 < (rho j) ^ 2 + q j z := by
      have := hr j
      have := (hq j z hz).1
      positivity
    exact (((contDiffAt_const (c := (rho j) ^ 2)).add hqz).rpow_const_of_ne
      hpos.ne').contDiffWithinAt
  have hF (j : ℕ) : Integrable (F j) ∧ (∫ z, F j z) = 0 :=
    suWeightedEuler_variation g b Metric.isOpen_ball (hu j) (hw j) (hrange j)
      hphi hphic hphis (heq j)
  obtain ⟨P0, hP0⟩ := hphic.exists_bound_of_continuous hphi.continuous
  obtain ⟨P1, hP1⟩ := (hphic.fderiv ℝ).exists_bound_of_continuous
    (hphi.continuous_fderiv (by simp))
  let P := max 0 (max P0 P1)
  have hP : 0 ≤ P := le_max_left _ _
  have hpb (z) : ‖phi z‖ ≤ P := (hP0 z).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hpdb (z) (i : Fin 2) : ‖fderiv ℝ phi z (e i)‖ ≤ P := by
    calc
      _ ≤ ‖fderiv ℝ phi z‖ * ‖e i‖ := (fderiv ℝ phi z).le_opNorm _
      _ = ‖fderiv ℝ phi z‖ := by simp
      _ ≤ P := (hP1 z).trans ((le_max_right _ _).trans (le_max_right _ _))
  let B := 2 * (2 * C * P * D ^ 2 + 4 * C * D * P)
  have hbound (j : ℕ) : ∀ᵐ z ∂mu, ‖F j z‖ ≤ B := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    have ha : (rho j) ^ 2 + q j z ≤ 2 := by
      have hs := sq_le_sq₀ (hr j).le (by norm_num : (0 : ℝ) ≤ 1) |>.mpr (hr1 j)
      nlinarith [(hq j z hz).2]
    have ha0 : 0 ≤ (rho j) ^ 2 + q j z := add_nonneg (sq_nonneg _) (hq j z hz).1
    have hw2 : w j z ≤ 2 := by
      calc
        _ ≤ (2 : ℝ) ^ c j := Real.rpow_le_rpow ha0 ha (hc0 j)
        _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (hc1 j)
        _ = 2 := Real.rpow_one _
    have hb := unweighted_variation_bound g b (u j) phi z hC hD hP
      (hcoeff j z hz).1 (hcoeff j z hz).2 (hgrad j z hz) (hpb z) (hpdb z)
    change ‖w j z * _‖ ≤ B
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ha0 _)]
    simpa only [suWeightedChartVariation, one_mul, B] using
      mul_le_mul hw2 hb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hpoint : ∀ᵐ z ∂mu, Tendsto (fun j => F j z) atTop (𝓝 (F0 z)) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact suWeightedChartVariation_tendsto g b u u0 phi lambda rho c z (hrange0 hz)
      (hlim z hz) (hdlim z hz) (hllim z hz) (hl0 z hz) (fun j => hl j z hz)
      hrho hr hc hc0
  have hm (j : ℕ) : AEStronglyMeasurable (F j) mu := (hF j).1.restrict.aestronglyMeasurable
  have hBm : Integrable (fun _ : LoopPlane => B) mu := integrable_const _
  have hF0m : AEStronglyMeasurable F0 mu := aestronglyMeasurable_of_tendsto_ae _ hm hpoint
  have hbound0 : ∀ᵐ z ∂mu, ‖F0 z‖ ≤ B := by
    have hb : ∀ᵐ z ∂mu, ∀ j, ‖F j z‖ ≤ B := ae_all_iff.mpr hbound
    filter_upwards [hpoint, hb] with z hz hzb
    exact le_of_tendsto hz.norm (Eventually.of_forall hzb)
  have hF0 : Integrable F0 mu := hBm.mono' hF0m hbound0
  have ht := tendsto_integral_of_dominated_convergence (fun _ => B) hm hBm hbound hpoint
  have hzero (j : ℕ) : (∫ z in O, F j z) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, (hF j).2]
    intro z hz
    have hnot : z ∉ tsupport phi := fun h => hz (hphis h)
    simp only [F, suWeightedChartVariation, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply, map_zero,
      Finset.sum_const_zero, mul_zero, add_zero]
  refine ⟨hF0, ?_⟩
  exact tendsto_nhds_unique ht (by simpa only [mu, hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

end PoincareConjecture.M60
