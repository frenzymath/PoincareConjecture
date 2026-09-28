import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_SphereVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.Proofs.M46

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem canonicalNeck_central_distance (q r : UnitTwoSphere) :
    g.edist (N.coordinate_map (q, 0)) (N.coordinate_map (r, 0)) ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon)) *
        canonicalSphereMetric.edist q r := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord (q : UnitTwoSphere) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map (q, 0) :=
    N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds ⟨mem_univ q, hzero⟩)
  let F : UnitTwoSphere → M := fun q => N.coordinate_map (q, 0)
  have hF : ContMDiff (𝓡 2) (𝓡 3) 1 F := by
    intro q
    exact ((hcoord q).comp q
      (contMDiffAt_id.prodMk contMDiffAt_const)).of_le (by simp)
  have hderiv (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      mfderiv (𝓡 2) (𝓡 3) F q v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, 0) (v, 0) := by
    dsimp only [TangentSpace] at v ⊢
    change mfderiv (𝓡 2) (𝓡 3)
      (N.coordinate_map ∘ fun q : UnitTwoSphere => (q, (0 : ℝ))) q v = _
    have h := mfderiv_comp_apply q ((hcoord q).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const) v
    simp only [id_eq, mfderiv_prod_left] at h
    exact h
  let C := N.scale * Real.sqrt (1 + N.epsilon)
  have hplus : 0 ≤ 1 + N.epsilon := by linarith [N.epsilon_pos]
  have hC : 0 < C := mul_pos N.scale_pos
    (Real.sqrt_pos.mpr (by linarith [N.epsilon_pos]))
  have hCsq : C ^ 2 = (1 + N.epsilon) * N.scale ^ 2 := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt hplus]
    ring
  have hbound (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v)
        (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
        C ^ 2 * canonicalSphereMetric.inner q v v := by
    have h := (N.pullback_metric_bounds (z := (q, 0)) hzero (v, 0)).2
    rw [hderiv, hCsq]
    simpa only [canonicalSphereMetric, rescaledMetric_inner, roundCylinderPullback,
      EvolvingRoundCylinderMetric,
      Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner,
      RiemannianMetric.euclideanMetric_inner, sub_zero, mul_one, zero_mul,
      add_zero, mul_assoc] using h
  exact canonicalSphereMetric.edist_le_mul_of_inner_mfderiv_le g hF hC hbound q r

noncomputable def canonicalNeckPatch (q : UnitTwoSphere) (a : ℝ) :
    Set RoundCylinderSpace :=
  canonicalSphereMetric.ball q a ×ˢ Ioo (-a) a

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem canonicalNeckPatch_subset_domain (q : UnitTwoSphere) {a : ℝ}
    (ha : a ≤ 1) : canonicalNeckPatch q a ⊆ N.cylinderDomain := by
  have hinv : 1 < N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ N.epsilon_pos).mpr
    linarith [N.epsilon_lt_half]
  intro z hz
  exact ⟨mem_univ _, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩

theorem canonicalNeckPatch_image_subset_ball (q : UnitTwoSphere)
    (hq : N.coordinate_map (q, 0) = N.center) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    N.coordinate_map '' canonicalNeckPatch q a ⊆ g.ball N.center (4 * N.scale * a) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hroot : Real.sqrt (1 + N.epsilon) < 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos]),
      Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  let C := N.scale * Real.sqrt (1 + N.epsilon)
  have hC : 0 ≤ C := mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  rintro x ⟨⟨r, z⟩, hz, rfl⟩
  have hdom := canonicalNeckPatch_subset_domain N q ha1 hz
  have hsphere := (canonicalNeck_central_distance N q r).trans
    (mul_le_mul' (le_refl (ENNReal.ofReal C)) hz.1.le)
  rw [← ENNReal.ofReal_mul hC] at hsphere
  have haxis := N.edist_coordinate_map_axis_le r hzero hdom.2
  simp only [sub_zero] at haxis
  have habs : |z| ≤ a := (abs_lt.mpr hz.2).le
  have haxis' := haxis.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left habs hC))
  change g.edist N.center (N.coordinate_map (r, z)) < ENNReal.ofReal _
  rw [← hq]
  calc
    _ ≤ g.edist (N.coordinate_map (q, 0)) (N.coordinate_map (r, 0)) +
        g.edist (N.coordinate_map (r, 0)) (N.coordinate_map (r, z)) :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (C * a) + ENNReal.ofReal (C * a) := add_le_add hsphere haxis'
    _ = ENNReal.ofReal (2 * C * a) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hC ha.le) (mul_nonneg hC ha.le)]
      congr 1
      ring
    _ < ENNReal.ofReal (4 * N.scale * a) := by
      apply (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) N.scale_pos) ha)).mpr
      have h := mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left hroot N.scale_pos) ha
      dsimp [C]
      nlinarith

end PoincareConjecture.Proofs.M46
