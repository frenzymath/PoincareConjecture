import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CalibratedRay
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_unit_tangent_mvfderiv_eq_neg_one_of_calibrated_point
    (g : RiemannianMetric n M) (hc : MetricComplete g) {f : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    {x : M} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    {y : M} (hxy : (g.edist x y).toReal = 1) (hfy : f y = f x - 1) :
    ∃ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v = 1 ∧ mvfderiv (𝓡 n) f x v = -1 := by
  obtain ⟨γ, hγ0, hγ1, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc x y
      (by rw [hxy]; norm_num)
  rw [hxy] at hγ1 hγ hspeed hmin
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hcal (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f (γ t) = f x - t := by
    have h0 := hLip (γ 0) (γ t)
    have h1 := hLip (γ t) (γ 1)
    rw [hmin 0 hzero t ht, ENNReal.toReal_ofReal (abs_nonneg _),
      zero_sub, abs_neg, abs_of_nonneg ht.1, hγ0] at h0
    rw [hmin t ht 1 hone, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub, hγ1, hfy] at h1
    linarith [(abs_le.mp h0).2, (abs_le.mp h1).2]
  subst x
  have hγd := (hγ.contMDiffAt hzero).mdifferentiableAt one_ne_zero
  let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1
  refine ⟨v, hspeed 0 hzero, ?_⟩
  have hd := (hf.hasMFDerivAt.comp 0 hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun t => f (γ t)) (mvfderiv (𝓡 n) f (γ 0) v) 0 at hd
  have hlin : HasDerivAt (fun t : ℝ => f (γ 0) - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub (f (γ 0))
  have hlin' : HasDerivWithinAt (fun t => f (γ t)) (-1) (Icc (0 : ℝ) 1) 0 :=
    hlin.hasDerivWithinAt.congr hcal (by simp)
  exact (hd.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc zero_lt_one 0 hzero)).symm.trans
      (hlin'.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 hzero))

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem gradient_norm_eq_one_of_calibrated_point
    (D : LeviCivitaData g) (hc : MetricComplete g) {f : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    {x : M} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    {y : M} (hxy : (g.edist x y).toReal = 1) (hfy : f y = f x - 1) :
    g.tangentNorm x (D.gradient f x) = 1 := by
  apply le_antisymm
  · exact D.gradient_norm_le_of_distance_lipschitz (C := 1)
      (by norm_num) (by simpa only [one_mul] using hLip) hf
  · obtain ⟨v, hv, hfv⟩ :=
      g.exists_unit_tangent_mvfderiv_eq_neg_one_of_calibrated_point hc hLip hf hxy hfy
    simpa only [hfv, abs_neg, abs_one, hv, mul_one] using
      D.abs_mvfderiv_le_gradient_norm f x v

omit [T3Space M] [PreconnectedSpace M] in


theorem eq_neg_gradient_of_unit_tangent_mvfderiv_eq_neg_one
    (D : LeviCivitaData g) {f : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    {x : M} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    {v : TangentSpace (𝓡 n) x} (hv : g.tangentNorm x v = 1)
    (hfv : mvfderiv (𝓡 n) f x v = -1) : v = -D.gradient f x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hupper := D.gradient_norm_le_of_distance_lipschitz (C := 1)
    (by norm_num) (by simpa only [one_mul] using hLip) hf
  have hlower : 1 ≤ g.tangentNorm x (D.gradient f x) := by
    simpa only [hfv, abs_neg, abs_one, hv, mul_one] using
      D.abs_mvfderiv_le_gradient_norm f x v
  have hnorm : ‖D.gradient f x‖ = 1 := le_antisymm hupper hlower
  have hvnorm : ‖v‖ = 1 := hv
  have hinner : inner ℝ v (D.gradient f x) = -1 := by
    rw [real_inner_comm]
    exact (D.inner_gradient f x v).trans hfv
  have hzero : ‖v + D.gradient f x‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hvnorm, hnorm, hinner]
    norm_num
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

omit [T3Space M] [PreconnectedSpace M] in



theorem tangent_eq_neg_gradient_of_calibrated_segment
    (D : LeviCivitaData g) {f : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hcal : ∀ t ∈ Icc 0 L, f (γ t) = f (γ 0) - t)
    {t : ℝ} (ht : t ∈ Icc 0 L)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 = -D.gradient f (γ t) := by
  apply D.eq_neg_gradient_of_unit_tangent_mvfderiv_eq_neg_one hLip hf (hspeed t ht)
  have hγd := (hγ.contMDiffAt ht).mdifferentiableAt one_ne_zero
  have hd := (hf.hasMFDerivAt.comp t hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun s => f (γ s))
    (mvfderiv (𝓡 n) f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) t at hd
  have hlin : HasDerivAt (fun s : ℝ => f (γ 0) - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (f (γ 0))
  have hlin' : HasDerivWithinAt (fun s => f (γ s)) (-1) (Icc (0 : ℝ) L) t :=
    hlin.hasDerivWithinAt.congr hcal (hcal t ht)
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hL t ht)).symm.trans
    (hlin'.derivWithin (uniqueDiffOn_Icc hL t ht))

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M]
  [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_ray_busemann_calibrated_segment
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) (x : M) {L : ℝ} (hL : 0 < L) :
    ∃ γ : ℝ → M, γ 0 = x ∧ g.IsGeodesicOn γ (Icc 0 L) ∧
      (∀ t ∈ Icc 0 L,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
      ∀ t ∈ Icc 0 L, busemann ray (γ t) = busemann ray x - t := by
  let : ProperSpace M := g.properSpace_of_complete hc hdist
  obtain ⟨coray, hcoray, hcoray0, hcal⟩ :=
    exists_calibrated_ray (g.hasMinimizingSegments_of_complete hc hdist) hray x
  have hxL : (g.edist x (coray L)).toReal = L := by
    rw [← hdist, ← hcoray0]
    simpa only [zero_sub, abs_neg, abs_of_nonneg hL.le] using
      hcoray (s := 0) le_rfl hL.le
  obtain ⟨γ, hγ0, hγL, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc x (coray L)
      (by rwa [hxL])
  rw [hxL] at hγL hγ hspeed hmin
  refine ⟨γ, hγ0, hγ, hspeed, hmin, ?_⟩
  intro t ht
  have hzero : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hend : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  have h0 := (lipschitz_busemann hray).dist_le_mul (γ 0) (γ t)
  have h1 := (lipschitz_busemann hray).dist_le_mul (γ t) (γ L)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, hdist] at h0 h1
  rw [hmin 0 hzero t ht, ENNReal.toReal_ofReal (abs_nonneg _),
    zero_sub, abs_neg, abs_of_nonneg ht.1, hγ0] at h0
  rw [hmin t ht L hend, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub, hγL, hcal L hL.le] at h1
  linarith [(abs_le.mp h0).2, (abs_le.mp h1).2]




theorem exists_ray_busemann_calibrated_segment_initial_tangent
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (busemann ray) x)
    {L : ℝ} (hL : 0 < L) :
    ∃ γ : ℝ → M, γ 0 = x ∧ g.IsGeodesicOn γ (Icc 0 L) ∧
      (∀ t ∈ Icc 0 L,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
      (∀ t ∈ Icc 0 L, busemann ray (γ t) = busemann ray x - t) ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = -D.gradient (busemann ray) (γ 0) := by
  obtain ⟨γ, hγ0, hγ, hspeed, hmin, hcal⟩ :=
    g.exists_ray_busemann_calibrated_segment hc hdist hray x hL
  refine ⟨γ, hγ0, hγ, hspeed, hmin, hcal, ?_⟩
  have hLip (p q : M) :
      |busemann ray p - busemann ray q| ≤ (g.edist p q).toReal := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hdist] using
      (lipschitz_busemann hray).dist_le_mul p q
  apply D.tangent_eq_neg_gradient_of_calibrated_segment hLip hL hγ hspeed
    (by simpa only [hγ0] using hcal) ⟨le_rfl, hL.le⟩
  simpa only [hγ0] using hf




theorem exists_ray_busemann_calibrated_segment_outside_compact
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (busemann ray) x)
    {K : Set M} (hK : IsCompact K) (T : ℝ) :
    ∃ (L : ℝ) (γ : ℝ → M), 0 < L ∧ T < L ∧ γ 0 = x ∧ γ L ∉ K ∧
      g.IsGeodesicOn γ (Icc 0 L) ∧
      (∀ t ∈ Icc 0 L,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
      (∀ t ∈ Icc 0 L, busemann ray (γ t) = busemann ray x - t) ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = -D.gradient (busemann ray) (γ 0) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall x
  let L := max (max R T) 0 + 1
  have hL : 0 < L := by dsimp [L]; linarith [le_max_right (max R T) 0]
  have hRL : R < L := by
    dsimp [L]
    linarith [(le_max_left R T).trans (le_max_left (max R T) 0)]
  have hTL : T < L := by
    dsimp [L]
    linarith [(le_max_right R T).trans (le_max_left (max R T) 0)]
  obtain ⟨γ, hγ0, hγ, hspeed, hmin, hcal, hinit⟩ :=
    g.exists_ray_busemann_calibrated_segment_initial_tangent D hc hdist hray hf hL
  refine ⟨L, γ, hL, hTL, hγ0, ?_, hγ, hspeed, hmin, hcal, hinit⟩
  intro hmem
  have hdistL : dist (γ L) x = L := by
    rw [dist_comm, ← hγ0, hdist, hmin 0 ⟨le_rfl, hL.le⟩ L ⟨hL.le, le_rfl⟩,
      ENNReal.toReal_ofReal (abs_nonneg _), zero_sub, abs_neg, abs_of_pos hL]
  have hbound := hR hmem
  rw [Metric.mem_closedBall, hdistL] at hbound
  exact (not_lt_of_ge hbound) hRL



theorem exists_ray_busemann_unit_calibrated_point
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) (x : M) :
    ∃ y : M, (g.edist x y).toReal = 1 ∧ busemann ray y = busemann ray x - 1 := by
  let : ProperSpace M := g.properSpace_of_complete hc hdist
  obtain ⟨coray, hcoray, hcoray0, hcal⟩ :=
    exists_calibrated_ray (g.hasMinimizingSegments_of_complete hc hdist) hray x
  refine ⟨coray 1, ?_, hcal 1 zero_le_one⟩
  rw [← hdist, ← hcoray0]
  simpa using hcoray (s := 0) le_rfl (t := 1) zero_le_one



theorem ray_busemann_gradient_norm_eq_one
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (busemann ray) x) :
    g.tangentNorm x (D.gradient (busemann ray) x) = 1 := by
  obtain ⟨y, hxy, hfy⟩ := g.exists_ray_busemann_unit_calibrated_point hc hdist hray x
  apply D.gradient_norm_eq_one_of_calibrated_point hc (f := busemann ray) _ hf hxy hfy
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hdist] using
    (lipschitz_busemann hray).dist_le_mul x y



theorem ae_ray_busemann_gradient_norm_eq_one
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) :
    ∀ᵐ x ∂g.volumeMeasure,
      g.tangentNorm x (D.gradient (busemann ray) x) = 1 := by
  have hLip (x y : M) :
      |busemann ray x - busemann ray y| ≤ (g.edist x y).toReal := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hdist] using
      (lipschitz_busemann hray).dist_le_mul x y
  filter_upwards [g.ae_mDifferentiableAt_of_distance_lipschitz hLip] with x hx
  exact g.ray_busemann_gradient_norm_eq_one D hc hdist hray hx

end PoincareConjecture.RiemannianMetric
