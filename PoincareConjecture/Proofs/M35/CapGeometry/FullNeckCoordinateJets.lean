import PoincareConjecture.Proofs.M35.Thm12_28.FullNeckMetricJets
import PoincareConjecture.Proofs.M35.Thm12_28.PointIsometryJets
import PoincareConjecture.Proofs.M35.Thm12_28.MetricChartCancellation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local notation "V" => EuclideanSpace ℝ (Fin 3)




theorem full_coordinate_jets_of_target_realization (N : EpsilonNeck g)
    (he : N.epsilon ≤ 1 / 24) {ι : Type*}
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (c : M) (hchart : ∀ i, N.coordinate_map (q i, s i) ∈ (extChartAt (𝓡 3) c).source)
    (K : Set V) (hK : IsCompact K)
    (hpoints : ∀ i, extChartAt (𝓡 3) c (N.coordinate_map (q i, s i)) ∈ K)
    (gB : RiemannianMetric 3 V)
    (hBmetric : ∀ i, ∀ᶠ y in 𝓝 (extChartAt (𝓡 3) c (N.coordinate_map (q i, s i))),
      gB.euclideanCoefficients y = N.scale⁻¹ ^ 2 •
        g.pullbackCoefficients (extChartAt (𝓡 3) c).symm y) :
    M35.HasUniformJetBoundsAt (⌊N.epsilon⁻¹⌋₊ + 1)
      (fun i => extChartAt (𝓡 3) c ∘ N.coordinate_map ∘ M35.cylinderChart (q i))
      (fun i => M35.cylinderCoordinateEquiv.symm (0, s i)) := by
  classical
  let p (i : ι) := M35.cylinderCoordinateEquiv.symm (0, s i)
  let f (i : ι) := N.coordinate_map ∘ M35.cylinderChart (q i)
  let psi (i : ι) := extChartAt (𝓡 3) c ∘ f i
  have hcenter (i : ι) : M35.cylinderChart (q i) (p i) = (q i, s i) := by
    have hq := (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).left_inv
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) (q i))
    rw [M35.sphere_chart_center] at hq
    simp only [M35.cylinderChart, p, ContinuousLinearEquiv.apply_symm_apply, hq]
  have hpsiCenter (i : ι) : psi i (p i) =
      extChartAt (𝓡 3) c (N.coordinate_map (q i, s i)) := by
    change extChartAt (𝓡 3) c (N.coordinate_map (M35.cylinderChart (q i) (p i))) = _
    rw [hcenter]
  have hp (i : ι) : (M35.cylinderCoordinateEquiv (p i)).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply] using hs i
  choose gA _D hAmetric using fun i =>
    N.exists_full_normalized_metric_realization (q i) (hp i)
  have hAmetric' : ∀ i, ∀ᶠ y in 𝓝 (p i),
      (gA i).euclideanCoefficients y = N.scale⁻¹ ^ 2 • g.pullbackCoefficients (f i) y :=
    hAmetric
  have hfj (i : ι) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f i) (p i) :=
    (N.full_euclidean_chart_regular (q i) (hp i)).1
  have hpsiRegular (i : ι) (y : V)
      (hy : (M35.cylinderCoordinateEquiv y).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (hc : f i y ∈ (extChartAt (𝓡 3) c).source) : ContDiffAt ℝ ∞ (psi i) y := by
    have hc' : f i y ∈ (chartAt V c).source := by
      rwa [← extChartAt_source (I := 𝓡 3)]
    exact ((contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hc').comp y
      (N.full_euclidean_chart_regular (q i) hy).1).contDiffAt
  have hchartCenter (i : ι) : f i (p i) ∈ (extChartAt (𝓡 3) c).source := by
    change N.coordinate_map (M35.cylinderChart (q i) (p i)) ∈ _
    rw [hcenter]
    exact hchart i
  have hpsiAt (i : ι) : ContDiffAt ℝ ∞ (psi i) (p i) :=
    hpsiRegular i (p i) (hp i) (hchartCenter i)
  have hnear (i : ι) : ∀ᶠ y in 𝓝 (p i),
      (M35.cylinderCoordinateEquiv y).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
        f i y ∈ (extChartAt (𝓡 3) c).source := by
    have hinterval : ∀ᶠ y in 𝓝 (p i),
        (M35.cylinderCoordinateEquiv y).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      (isOpen_Ioo.preimage
        (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)).mem_nhds (hp i)
    exact hinterval.and
      ((hfj i).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓡 3) c).mem_nhds (hchartCenter i)))
  have hAj := N.full_normalized_realization_jets q s hs gA hAmetric'
  have hBcont : Continuous gB.euclideanCoefficients :=
    continuous_iff_continuousAt.mpr (fun y => (gB.contDiffAt_euclideanCoefficients y).continuousAt)
  obtain ⟨b, hb, hBlower⟩ := exists_uniform_bilinear_lower_bound hK hBcont.continuousOn
    (fun y _ v hv => gB.pos y v hv)
  let a := min (1 / 2 : ℝ) b
  have ha : 0 < a := lt_min (by norm_num) hb
  have hAlow (i : ι) (v : V) : a * ‖v‖ ^ 2 ≤ (gA i).euclideanCoefficients (p i) v v := by
    rw [(hAmetric' i).self_of_nhds]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
      (N.full_normalized_metric_lower he (q i) (s i) (hs i) v)
  have hBlow (i : ι) (v : V) : a * ‖v‖ ^ 2 ≤ gB.euclideanCoefficients (psi i (p i)) v v :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
      (hBlower _ ((hpsiCenter i).symm ▸ hpoints i) v)
  have hBj : M35.HasUniformJetBoundsAt ⌊N.epsilon⁻¹⌋₊
      (fun _ : ι => gB.euclideanCoefficients) (fun i => psi i (p i)) := by
    intro r _
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (fun y _ =>
      ((gB.contDiffAt_euclideanCoefficients y).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top (a := (r : ℕ∞)))).continuousWithinAt)
    refine ⟨C, fun i => hC _ ?_⟩
    change psi i (p i) ∈ K
    rw [hpsiCenter]
    exact hpoints i
  have hzero : ∃ C : ℝ, ∀ i, ‖psi i (p i)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuousOn_id
    refine ⟨C, fun i => hC _ ?_⟩
    change psi i (p i) ∈ K
    rw [hpsiCenter]
    exact hpoints i
  have hmetric (i : ι) : ∀ᶠ y in 𝓝 (p i), ∀ v w : V,
      gB.euclideanCoefficients (psi i y) (fderiv ℝ (psi i) y v)
        (fderiv ℝ (psi i) y w) = (gA i).euclideanCoefficients y v w := by
    have hB := (hpsiAt i).continuousAt.tendsto.eventually
      ((hpsiCenter i).symm ▸ hBmetric i)
    filter_upwards [hnear i, hAmetric' i, hB] with y hy hAy hBy
    intro v w
    have hcy : f i y ∈ (chartAt V c).source := by
      rw [← extChartAt_source (I := 𝓡 3)]
      exact hy.2
    have hd := mfderiv_comp y
      ((contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hcy).mdifferentiableAt (by simp))
      ((N.full_euclidean_chart_regular (q i) hy.1).1.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    rw [hBy, hAy]
    change N.scale⁻¹ ^ 2 * g.pullbackCoefficients (extChartAt (𝓡 3) c).symm
      (extChartAt (𝓡 3) c (f i y)) (fderiv ℝ (psi i) y v) (fderiv ℝ (psi i) y w) =
      N.scale⁻¹ ^ 2 * g.inner (f i y) (mfderiv (𝓡 3) (𝓡 3) (f i) y v)
        (mfderiv (𝓡 3) (𝓡 3) (f i) y w)
    rw [show fderiv ℝ (psi i) y =
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) c) (f i y)).comp
        (mfderiv (𝓡 3) (𝓡 3) (f i) y) from hd]
    exact congrArg (fun z : ℝ => N.scale⁻¹ ^ 2 * z)
      (g.chartCoefficients_cancel c hy.2 _ _)
  have hfloor : 1 ≤ ⌊N.epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    rw [one_le_inv₀ N.epsilon_pos]
    linarith
  have horder : ⌊N.epsilon⁻¹⌋₊ - 1 + 1 = ⌊N.epsilon⁻¹⌋₊ := by omega
  have hbound := M35.finite_local_isometry_jets_at
    (n := ⌊N.epsilon⁻¹⌋₊ - 1)
    (fun i y => (gA i).contDiffAt_euclideanCoefficients y)
    (fun (_ : ι) y => gB.contDiffAt_euclideanCoefficients y)
    (fun i y => (gA i).inner_isInvertible y)
    (fun (_ : ι) y => gB.inner_isInvertible y)
    (fun (_ : ι) y v w => gB.symm y v w)
    (fun i => (hnear i).mono (fun y hy => hpsiRegular i y hy.1 hy.2))
    ha hAlow hBlow (horder.symm ▸ hAj) (horder.symm ▸ hBj) hzero hmetric
  have horder' : ⌊N.epsilon⁻¹⌋₊ - 1 + 2 = ⌊N.epsilon⁻¹⌋₊ + 1 := by omega
  exact horder' ▸ hbound

end PoincareConjecture.EpsilonNeck
