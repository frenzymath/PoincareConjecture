import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.MetricDifferential
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

private theorem inner_self_nonnegative (g : RiemannianMetric 3 M) (x : M)
    (v : TangentSpace (𝓡 3) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

theorem m67_gram_det_le_of_differential_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : M → N) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x v,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        c * g.inner x v v)
    (x : M) (u v : TangentSpace (𝓡 3) x) :
    let L := mfderiv (𝓡 3) (𝓡 3) f x
    h.inner (f x) (L u) (L u) * h.inner (f x) (L v) (L v) -
        (h.inner (f x) (L u) (L v)) ^ 2 ≤
      c ^ 2 * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  dsimp only
  let L := mfderiv (𝓡 3) (𝓡 3) f x
  by_cases hu : u = 0
  · simp [hu]
  have hgu : 0 < g.inner x u u := g.pos x u hu
  let a := g.inner x u v / g.inner x u u
  let w := v - a • u
  have hgidentity : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 =
      g.inner x u u * g.inner x w w - (g.inner x u w) ^ 2 := by
    dsimp [w]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [g.symm x v u]
    ring
  have hhidentity : h.inner (f x) (L u) (L u) * h.inner (f x) (L v) (L v) -
      (h.inner (f x) (L u) (L v)) ^ 2 =
      h.inner (f x) (L u) (L u) * h.inner (f x) (L w) (L w) -
        (h.inner (f x) (L u) (L w)) ^ 2 := by
    dsimp [w]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [h.symm (f x) (L v) (L u)]
    ring
  have horth : g.inner x u w = 0 := by
    dsimp [w, a]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  change h.inner (f x) (L u) (L u) * h.inner (f x) (L v) (L v) -
    (h.inner (f x) (L u) (L v)) ^ 2 ≤ _
  rw [hhidentity, hgidentity, horth, zero_pow (by decide : 2 ≠ 0), sub_zero]
  calc
    _ ≤ h.inner (f x) (L u) (L u) * h.inner (f x) (L w) (L w) :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ (c * g.inner x u u) * (c * g.inner x w w) :=
      mul_le_mul (hbound x u) (hbound x w) (inner_self_nonnegative h (f x) (L w))
        (mul_nonneg hc hgu.le)
    _ = _ := by ring

theorem m67_area_density_comp_le [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    {f : M → N} (hf : MDifferentiable (𝓡 3) (𝓡 3) f)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * g.edist x y)
    {d : LoopPlane → M} {z : LoopPlane}
    (hd : MDifferentiableAt (𝓡 2) (𝓡 3) d z) :
    parametrizedAreaDensity h (f ∘ d) z ≤ L ^ 2 * parametrizedAreaDensity g d z := by
  let e := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 3) d z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hdet := m67_gram_det_le_of_differential_le g h f (sq_nonneg L)
    (m67_inner_mfderiv_le_of_distance_bound g h hf hL hbound) (d z) (e 0) (e 1)
  have hdet' : Matrix.det (m60AreaGram h (f ∘ d) z) ≤
      (L ^ 2) ^ 2 * Matrix.det (m60AreaGram g d z) := by
    unfold m60AreaGram
    rw [mfderiv_comp z (hf (d z)) hd, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    rw [h.symm (f (d z)) (mfderiv (𝓡 3) (𝓡 3) f (d z) (e 1))
      (mfderiv (𝓡 3) (𝓡 3) f (d z) (e 0)), g.symm (d z) (e 1) (e 0)]
    simpa only [pow_two] using hdet
  change Real.sqrt (max 0 (Matrix.det (m60AreaGram h (f ∘ d) z))) ≤
    L ^ 2 * Real.sqrt (max 0 (Matrix.det (m60AreaGram g d z)))
  rw [max_eq_right (m60AreaGram_det_nonneg h (f ∘ d) z),
    max_eq_right (m60AreaGram_det_nonneg g d z)]
  calc
    _ ≤ Real.sqrt ((L ^ 2) ^ 2 * Matrix.det (m60AreaGram g d z)) := Real.sqrt_le_sqrt hdet'
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg L)]

end PoincareConjecture
