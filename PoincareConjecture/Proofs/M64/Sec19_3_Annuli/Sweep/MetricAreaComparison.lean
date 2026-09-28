import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.MetricTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64_gram_pair_le_of_metric_le
    (g h : RiemannianMetric n M) (x : M) {D : ℝ} (hD : 0 ≤ D)
    (hcompare : ∀ v : TangentSpace (𝓡 n) x, h.inner x v v ≤ D * g.inner x v v)
    (u v : TangentSpace (𝓡 n) x) :
    h.inner x u u * h.inner x v v - (h.inner x u v) ^ 2 ≤
      D ^ 2 * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  by_cases hu : u = 0
  · subst u
    simp
  have hpos : 0 < g.inner x u u := g.pos x u hu
  have hne : g.inner x u u ≠ 0 := ne_of_gt hpos
  let q := g.inner x u v / g.inner x u u
  let w := v - q • u
  have hinvariant (m : RiemannianMetric n M) :
      m.inner x u u * m.inner x v v - (m.inner x u v) ^ 2 =
        m.inner x u u * m.inner x w w - (m.inner x u w) ^ 2 := by
    dsimp only [w]
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
    rw [m.symm x v u]
    ring
  have horth : g.inner x u w = 0 := by
    dsimp only [w, q]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have hgu : 0 ≤ g.inner x u u := hpos.le
  have hhw : 0 ≤ h.inner x w w := (h.toRiemannianMetric.toCore x).re_inner_nonneg _
  calc
    _ = h.inner x u u * h.inner x w w - (h.inner x u w) ^ 2 := hinvariant h
    _ ≤ h.inner x u u * h.inner x w w := sub_le_self _ (sq_nonneg _)
    _ ≤ (D * g.inner x u u) * (D * g.inner x w w) :=
      mul_le_mul (hcompare u) (hcompare w) hhw (mul_nonneg hD hgu)
    _ = D ^ 2 * (g.inner x u u * g.inner x w w - (g.inner x u w) ^ 2) := by
      rw [horth]
      ring
    _ = _ := by rw [← hinvariant g]

theorem m64AreaDensity_le_of_tangentNorm_le
    (g h : RiemannianMetric n M) {C : ℝ} (_hC : 0 ≤ C)
    (hcompare : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v)
    (f : LoopPlane → M) (p : LoopPlane) :
    m60AreaDensity h f p ≤ C ^ 2 * m60AreaDensity g f p := by
  have hquadratic (x : M) (v : TangentSpace (𝓡 n) x) :
      h.inner x v v ≤ C ^ 2 * g.inner x v v := by
    have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hcompare x v) 2
    have hgp : 0 ≤ g.inner x v v := (g.toRiemannianMetric.toCore x).re_inner_nonneg v
    have hhp : 0 ≤ h.inner x v v := (h.toRiemannianMetric.toCore x).re_inner_nonneg v
    change (Real.sqrt (h.inner x v v)) ^ 2 ≤
      (C * Real.sqrt (g.inner x v v)) ^ 2 at hsquare
    rw [mul_pow, Real.sq_sqrt hgp, Real.sq_sqrt hhp] at hsquare
    exact hsquare
  have hdet : Matrix.det (m60AreaGram h f p) ≤
      (C ^ 2) ^ 2 * Matrix.det (m60AreaGram g f p) := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two,
      m60AreaGram_symm h f p 1 0, m60AreaGram_symm g f p 1 0]
    simpa only [m60AreaGram, pow_two] using
      m64_gram_pair_le_of_metric_le g h (f p) (sq_nonneg C) (hquadratic (f p))
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  simp only [m60AreaDensity, max_eq_right (m60AreaGram_det_nonneg h f p),
    max_eq_right (m60AreaGram_det_nonneg g f p)]
  calc
    _ ≤ Real.sqrt ((C ^ 2) ^ 2 * Matrix.det (m60AreaGram g f p)) :=
      Real.sqrt_le_sqrt hdet
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg C)]

theorem m64Annulus_transport_metric_area [T2Space M]
    (g h : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {C : ℝ} (hC : 0 < C)
    (hcompare : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v) :
    ∃ B : M64Annulus h c0 c1, B.map = A.map ∧ B.area ≤ C ^ 2 * A.area := by
  have hdist (x y : M) : h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
    apply RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le g h
      (F := id) contMDiff_id hC
    intro q v
    simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using hcompare q v
  obtain ⟨B, hmap⟩ := m64Annulus_transport_metric g h A hC.le hdist
  refine ⟨B, hmap, ?_⟩
  change (∫ p in m64AnnulusDomain, m60AreaDensity h B.map p) ≤ _
  calc
    _ ≤ ∫ p in m64AnnulusDomain, C ^ 2 * m60AreaDensity g A.map p :=
      integral_mono B.area_integrable (A.area_integrable.const_mul (C ^ 2)) (fun p => by
        rw [hmap]
        exact m64AreaDensity_le_of_tangentNorm_le g h hC.le hcompare A.map p)
    _ = _ := integral_const_mul _ _

theorem m64Annulus_transport_time_area [T2Space M]
    {a b : ℝ} (F : RicciFlow n M (Icc a b)) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric s) c0 c1) :
    ∃ B : M64Annulus (F.metric t) c0 c1, B.map = A.map ∧
      B.area ≤ Real.exp ((n : ℝ) * K * |t - s|) ^ 2 * A.area :=
  m64Annulus_transport_metric_area (F.metric s) (F.metric t) A (Real.exp_pos _)
    (m64_flow_tangentNorm_time_comparison F hK hcurv hs ht)

end PoincareConjecture
