import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.LocalChart







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}

private theorem polarMap_eq_homothety
    (d : UnitSliceRadialChartData hcomparison n) (c r : ℝ≥0) (hc : 0 < c) (hr : 0 < r)
    (w : ℝ × d.Level) (hw : 0 < w.1)
    (htarget : asymptoticConeDilation hcomparison (Real.toNNReal (w.1 / r))
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) w.2)) ∈ d.ambientChart.target) :
    d.polarMap c w =
      ((d.dilate (r / c) (div_pos hr hc)).ambientChart.trans d.ambientChart.symm)
        (d.polarMap r w) := by
  have hc' : 0 < (c : ℝ) := hc
  have hr' : 0 < (r : ℝ) := hr
  have hcone : d.ambientChart (d.polarMap r w) = asymptoticConeDilation hcomparison
      (Real.toNNReal (w.1 / r)) (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) w.2)) := by
    change d.ambientChart (d.ambientChart.symm (asymptoticConeDilation hcomparison
      (Real.toNNReal (1 + (w.1 / r - 1))) _)) = _
    rw [show 1 + (w.1 / r - 1) = w.1 / r by ring]
    exact d.ambientChart.right_inv htarget
  change _ = d.ambientChart.symm
    (asymptoticConeDilation hcomparison (r / c) (d.ambientChart (d.polarMap r w)))
  rw [hcone, asymptoticConeDilation_mul]
  have hscale : (r / c) * Real.toNNReal (w.1 / r) = Real.toNNReal (w.1 / c) := by
    ext
    simp only [NNReal.coe_mul, NNReal.coe_div,
      Real.coe_toNNReal _ (div_pos hw hr').le, Real.coe_toNNReal _ (div_pos hw hc').le]
    field_simp
  rw [hscale]
  change d.ambientChart.symm (asymptoticConeDilation hcomparison
    (Real.toNNReal (1 + (w.1 / c - 1))) _) = _
  rw [show 1 + (w.1 / c - 1) = w.1 / c by ring]



theorem inner_polarMap_at
    (d : UnitSliceRadialChartData hcomparison n) (c r : ℝ≥0) (hc : 0 < c) (hr : 0 < r)
    (z : d.Level)
    (htarget : asymptoticConeDilation hcomparison (r / c)
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) z)) ∈ d.ambientChart.target)
    (a b : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    letI : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    (d.dilate c hc).metric.inner (d.polarMap c ((r : ℝ), z))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) ((r : ℝ), z) (a, v))
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (d.polarMap c) ((r : ℝ), z) (b, w)) =
        a * b + (r : ℝ) ^ 2 *
          (RiemannianMetric.regularLevelMetric d.smooth d.source d.regular (1 / 2) d.metric).inner z v w := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let q : ℝ × d.Level := ((r : ℝ), z)
  let x := openLevelIncl d.potential d.source (1 / 2) z
  let T := (d.dilate (r / c) (div_pos hr hc)).ambientChart.trans d.ambientChart.symm
  have hxT : x ∈ T.source := ⟨z.1.2, htarget⟩
  have hcenter : d.polarMap r q = x := d.radiusCoordinate_center hr z.1.2
  obtain ⟨P, hqP, _, _, hP, _, _, _, _⟩ := d.exists_polar_openPartialHomeomorph r hr z
  have heq : d.polarMap c =ᶠ[𝓝 q] T ∘ d.polarMap r := by
    filter_upwards [P.open_source.mem_nhds hqP] with u hu
    exact d.polarMap_eq_homothety c r hc hr u (hP u hu).1 (hP u hu).2.2
  obtain ⟨hTsmooth, _, hTmetric⟩ := d.smooth_homothety_in_radial_charts d (r / c) (div_pos hr hc)
  have hTdiff : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) T (d.polarMap r q) := by
    rw [hcenter]
    exact (hTsmooth.contMDiffAt (T.open_source.mem_nhds hxT)).mdifferentiableAt (by simp)
  have hderiv : mfderiv I (𝓡 (n + 1)) (d.polarMap c) q =
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x).comp
        (mfderiv I (𝓡 (n + 1)) (d.polarMap r) q) := by
    rw [heq.mfderiv_eq, mfderiv_comp q hTdiff ((d.contMDiffAt_polarMap hr z).mdifferentiableAt (by simp)), hcenter]
  have hvalue : d.polarMap c q = T x := by
    rw [← hcenter]
    exact heq.eq_of_nhds
  let A := mfderiv I (𝓡 (n + 1)) (d.polarMap r) q
  have hinner := hTmetric x hxT (A (a, v)) (A (b, w))
  have hreference := d.inner_polarMap r hr z a b v w
  rw [d.dilate_inner] at hreference
  change (d.dilate c hc).metric.inner (d.polarMap c q)
    (mfderiv I (𝓡 (n + 1)) (d.polarMap c) q (a, v))
    (mfderiv I (𝓡 (n + 1)) (d.polarMap c) q (b, w)) = _
  rw [d.dilate_inner]
  erw [hvalue, hderiv]
  change (c : ℝ) ^ 2 * d.metric.inner (T x)
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x (A (a, v)))
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x (A (b, w))) = _
  rw [hinner]
  have hscale : (c : ℝ) ^ 2 * ((r / c : ℝ≥0) : ℝ) ^ 2 = (r : ℝ) ^ 2 := by
    rw [NNReal.coe_div]
    field_simp
  rw [← mul_assoc, hscale]
  rw [hcenter] at hreference
  exact hreference



theorem exists_smooth_polar_coordinates
    (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c) (z : d.Level) :
    letI : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    ∃ Q : OpenPartialHomeomorph (ℝ × d.Level) (UnitSliceAmbient n),
      ((c : ℝ), z) ∈ Q.source ∧
      Q ((c : ℝ), z) = openLevelIncl d.potential d.source (1 / 2) z ∧
      Q.target ⊆ d.ambientChart.source ∧
      (∀ q ∈ Q.source, 0 < q.1 ∧ Q q = d.polarMap c q) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ Q Q.source ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ Q.symm Q.target ∧
      (∀ y ∈ Q.target,
        (Q.symm y).1 = (c : ℝ) * (asymptoticConeRadius hcomparison (d.ambientChart y) : ℝ)) ∧
      (∀ y ∈ Q.target,
        d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (Q.symm y).2) =
          asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison (d.ambientChart y))⁻¹
            (d.ambientChart y)) ∧
      ∀ q ∈ Q.source, ∀ a b : ℝ, ∀ v w : EuclideanSpace ℝ (Fin n),
        (d.dilate c hc).metric.inner (Q q)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) Q q (a, v))
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) Q q (b, w)) =
            a * b + q.1 ^ 2 *
              (RiemannianMetric.regularLevelMetric d.smooth d.source d.regular (1 / 2) d.metric).inner q.2 v w := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨Q, hzQ, hQz, htarget, hQ, hsmooth, hinverse, hradius, hangle⟩ :=
    d.exists_smooth_polar_openPartialHomeomorph c hc z
  refine ⟨Q, hzQ, hQz, htarget, hQ, hsmooth, hinverse, hradius, hangle, ?_⟩
  intro q hq a b v w
  let r : ℝ≥0 := ⟨q.1, (hQ q hq).1.le⟩
  have hr : 0 < r := (hQ q hq).1
  have hc' : 0 < (c : ℝ) := hc
  have hy := Q.map_source hq
  have hradiusq := hradius (Q q) hy
  have hangleq := hangle (Q q) hy
  rw [Q.left_inv hq] at hradiusq hangleq
  have hscale : r / c = asymptoticConeRadius hcomparison (d.ambientChart (Q q)) := by
    ext
    rw [NNReal.coe_div]
    change q.1 / (c : ℝ) = _
    rw [hradiusq]
    field_simp
  have hcone : asymptoticConeDilation hcomparison (r / c)
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) ∈ d.ambientChart.target := by
    rw [hangleq, ← hscale, asymptoticConeDilation_mul,
      mul_inv_cancel₀ (div_pos hr hc).ne', asymptoticConeDilation_one]
    exact d.ambientChart.map_source (htarget hy)
  have heq : (Q : ℝ × d.Level → UnitSliceAmbient n) =ᶠ[𝓝 q] d.polarMap c := by
    filter_upwards [Q.open_source.mem_nhds hq] with u hu
    exact (hQ u hu).2
  have hderiv := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) (I' := 𝓡 (n + 1))
  erw [(hQ q hq).2, hderiv]
  exact d.inner_polarMap_at c r hc hr q.2 hcone a b v w

end Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData
