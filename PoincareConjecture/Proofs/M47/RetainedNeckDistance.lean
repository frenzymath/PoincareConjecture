import PoincareConjecture.Proofs.M36.NeckCoordinates
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_NeckPatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}

private theorem neck_inv_epsilon_gt_one : 1 < I.neck.epsilon⁻¹ := by
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ I.neck.epsilon_pos).mpr
  linarith [I.neck.epsilon_lt_half]

private theorem retained_coordinate_smooth_at (R : MetricSurgeryResult g0 I)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-I.neck.epsilon⁻¹) 1) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (R.collapse ∘ I.neck.coordinate_map) z := by
  have hdom : z ∈ I.neck.cylinderDomain :=
    ⟨mem_univ _, hz.1, hz.2.trans neck_inv_epsilon_gt_one⟩
  have hx : I.neck.coordinate_map z ∈ I.neck.region (-I.neck.epsilon⁻¹) 1 := by
    refine ⟨M36.neck_coordinate_mem I.neck z hdom, ?_⟩
    simpa only [M36.neck_inverse_coordinate I.neck z hdom, mem_Ioo] using hz
  exact (R.retained_smooth.contMDiffAt
    ((M36.neck_region_isOpen I.neck _ _).mem_nhds hx)).comp z
      (M36.neck_coordinate_contMDiffAt I.neck hdom)

private theorem retained_coordinate_pullback (R : MetricSurgeryResult g0 I)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioc (-I.neck.epsilon⁻¹) 0)
    (v : RoundCylinderTangent z) :
    roundCylinderPullback R.metric (R.collapse ∘ I.neck.coordinate_map) z v v =
      roundCylinderPullback g I.neck.coordinate_map z v v := by
  have hdom : z ∈ I.neck.cylinderDomain :=
    ⟨mem_univ _, hz.1, hz.2.trans_lt (inv_pos.mpr I.neck.epsilon_pos)⟩
  have hx : I.neck.coordinate_map z ∈ I.neck.region (-I.neck.epsilon⁻¹) 1 := by
    refine ⟨M36.neck_coordinate_mem I.neck z hdom, ?_⟩
    simpa only [M36.neck_inverse_coordinate I.neck z hdom, mem_Ioo] using
      (show z.2 ∈ Ioo (-I.neck.epsilon⁻¹) 1 from ⟨hz.1, hz.2.trans_lt zero_lt_one⟩)
  have hret : I.neck.coordinate_map z ∈
      I.neck.region (-I.neck.epsilon⁻¹) 0 ∪ I.neck.central_sphere := by
    apply (M36.neck_retained_iff I.neck).mpr
    refine ⟨hx.1, ?_⟩
    simpa only [M36.neck_inverse_coordinate I.neck z hdom] using hz.2
  have hf := (R.retained_smooth.contMDiffAt
    ((M36.neck_region_isOpen I.neck _ _).mem_nhds hx)).mdifferentiableAt (by simp)
  have hi := (M36.neck_coordinate_contMDiffAt I.neck hdom).mdifferentiableAt (by simp)
  have hd := mfderiv_comp_apply z hf hi v
  dsimp only [roundCylinderPullback]
  rw [hd]
  exact R.retained_metric _ hret _ _

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem retained_central_distance (R : MetricSurgeryResult g0 I)
    (q r : UnitTwoSphere) :
    R.metric.edist (R.collapse (I.neck.coordinate_map (q, 0)))
      (R.collapse (I.neck.coordinate_map (r, 0))) ≤
      ENNReal.ofReal (I.neck.scale * Real.sqrt (1 + I.neck.epsilon)) *
        M46.canonicalSphereMetric.edist q r := by
  let N := I.neck
  let theta := R.collapse ∘ N.coordinate_map
  have hzero : (0 : ℝ) ∈ Ioc (-N.epsilon⁻¹) 0 :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), le_rfl⟩
  have hcoord (q : UnitTwoSphere) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ theta (q, 0) :=
    retained_coordinate_smooth_at R ⟨hzero.1, zero_lt_one⟩
  let F : UnitTwoSphere → R.output.carrier := fun q => theta (q, 0)
  have hF : ContMDiff (𝓡 2) (𝓡 3) 1 F := by
    intro q
    exact ((hcoord q).comp q
      (contMDiffAt_id.prodMk contMDiffAt_const)).of_le
        (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hderiv (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      mfderiv (𝓡 2) (𝓡 3) F q v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) theta (q, 0) (v, 0) := by
    dsimp only [TangentSpace] at v ⊢
    change mfderiv (𝓡 2) (𝓡 3)
      (theta ∘ fun q : UnitTwoSphere => (q, (0 : ℝ))) q v = _
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
      R.metric.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v)
        (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
        C ^ 2 * M46.canonicalSphereMetric.inner q v v := by
    have h := (N.pullback_metric_bounds (z := (q, 0))
      ⟨hzero.1, inv_pos.mpr N.epsilon_pos⟩ (v, 0)).2
    rw [← retained_coordinate_pullback R hzero (v, 0)] at h
    rw [hderiv, hCsq]
    simpa only [F, theta, M46.canonicalSphereMetric, rescaledMetric_inner,
      roundCylinderPullback, EvolvingRoundCylinderMetric,
      Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner,
      RiemannianMetric.euclideanMetric_inner, sub_zero, mul_one, zero_mul,
      add_zero, mul_assoc] using h
  exact M46.canonicalSphereMetric.edist_le_mul_of_inner_mfderiv_le R.metric hF hC hbound q r

theorem retained_axial_distance (R : MetricSurgeryResult g0 I)
    (q : UnitTwoSphere) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 0) :
    R.metric.edist (R.collapse (I.neck.coordinate_map (q, 0)))
      (R.collapse (I.neck.coordinate_map (q, z))) ≤
      ENNReal.ofReal (I.neck.scale * Real.sqrt (1 + I.neck.epsilon) * |z|) := by
  let N := I.neck
  let theta := R.collapse ∘ N.coordinate_map
  let gamma : ℝ → R.output.carrier := fun t => theta (q, t)
  let C := N.scale * Real.sqrt (1 + N.epsilon)
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma (Ioo (-N.epsilon⁻¹) 1) := by
    intro t ht
    exact ((retained_coordinate_smooth_at R (z := (q, t)) ht).comp t
      (contMDiffAt_const.prodMk contMDiffAt_id)).contMDiffWithinAt
  have hI : Icc z 0 ⊆ Ioo (-N.epsilon⁻¹) 1 := by
    intro t ht
    constructor <;> linarith [hz.1, ht.1, ht.2, neck_inv_epsilon_gt_one (I := I)]
  have hspeed (t : ℝ) (ht : t ∈ Icc z 0) :
      R.metric.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1) ≤ C := by
    have hcoord := retained_coordinate_smooth_at R (z := (q, t)) (hI ht)
    have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1 =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) theta (q, t) (0, 1) := by
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (theta ∘ fun t : ℝ => (q, t)) t 1 = _
      rw [mfderiv_comp_apply t (hcoord.mdifferentiableAt (by simp))
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
      simp only [mfderiv_prod_right]
      rfl
    have h := (N.pullback_metric_bounds (z := (q, t))
      ⟨(hI ht).1, ht.2.trans_lt (inv_pos.mpr N.epsilon_pos)⟩ (0, 1)).2
    rw [← retained_coordinate_pullback R ⟨(hI ht).1, ht.2⟩ (0, 1)] at h
    have hinner : R.metric.inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1) ≤ C ^ 2 := by
      rw [hd]
      dsimp only [C]
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos])]
      simpa only [gamma, theta, roundCylinderPullback, EvolvingRoundCylinderMetric,
        Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner,
        RiemannianMetric.euclideanMetric_inner, map_zero, inner_zero_left,
        mul_zero, zero_mul, zero_add, one_mul, mul_one, mul_comm] using h
    exact (Real.sqrt_le_sqrt hinner).trans_eq
      (Real.sqrt_sq (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)))
  have h := R.metric.edist_le_of_tangentNorm_le hz.2 isOpen_Ioo hI hgamma
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) hspeed
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : R.output.carrier → Type _) :=
    ⟨R.metric.toRiemannianMetric⟩
  change R.metric.edist (gamma 0) (gamma z) ≤ _
  rw [show R.metric.edist (gamma 0) (gamma z) = R.metric.edist (gamma z) (gamma 0) from
    Manifold.riemannianEDist_comm]
  simpa only [zero_sub, abs_of_nonpos hz.2] using h

end PoincareConjecture.Proofs.M47
