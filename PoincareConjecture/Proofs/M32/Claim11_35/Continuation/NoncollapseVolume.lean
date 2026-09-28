import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.NoncollapseMetric
import PoincareConjecture.Proofs.M32.Claim11_32.NeckVolumeSmallBalls
import PoincareConjecture.Proofs.M32.Claim11_34.CylinderOpen
import PoincareConjecture.Proofs.M32.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.M15.Thm1_34_Calibration





















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set MeasureTheory Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (N : GeneralizedStrongNeck F t epsilon) (hepsilon : epsilon ≤ 1 / 200)
  {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) (hhalf : -(1 / 2 : ℝ) ≤ tau)

private def backwardNeckCoordinate :
    RoundCylinderSpace → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier :=
  fun z => N.time_cylinder.forward tau htau (N.coordinate_map z)

include hepsilon in
private theorem backwardNeckCoordinate_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (backwardNeckCoordinate N htau) (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
  let N0 := spatialNeck N (show epsilon < 1 / 2 by linarith)
  exact (N.time_cylinder.forward_smooth tau htau).comp N.coordinate_map_smooth
    (fun z hz => N0.coordinate_map_mem hz)

include hepsilon in
private theorem backwardNeck_pullback_lower
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : RoundCylinderTangent z) :
    (N.scale / 2) ^ 2 * EvolvingRoundCylinderMetric 0 z v v ≤
      roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) z v v := by
  have h := (abs_le.mp (strongNeck_evolving_pullback_quadratic_error N htau hz v)).1
  have hsphere : 0 ≤ (roundSphereMetric 2).inner z.1 v.1 v.1 := by
    rw [roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner]
    exact real_inner_self_nonneg
  have hzero : 0 ≤ EvolvingRoundCylinderMetric 0 z v v := by
    change 0 ≤ 2 * (1 - 0) * (roundSphereMetric 2).inner z.1 v.1 v.1 + v.2 * v.2
    nlinarith [mul_self_nonneg v.2]
  have hmodel : EvolvingRoundCylinderMetric 0 z v v ≤
      EvolvingRoundCylinderMetric tau z v v := by
    change 2 * (1 - 0) * (roundSphereMetric 2).inner z.1 v.1 v.1 + v.2 * v.2 ≤
      2 * (1 - tau) * (roundSphereMetric 2).inner z.1 v.1 v.1 + v.2 * v.2
    nlinarith [mul_nonpos_of_nonpos_of_nonneg htau.2 hsphere]
  have herr : 36 * epsilon * EvolvingRoundCylinderMetric 0 z v v ≤
      (3 / 4 : ℝ) * EvolvingRoundCylinderMetric 0 z v v :=
    mul_le_mul_of_nonneg_right (by linarith) hzero
  have hnormalized : EvolvingRoundCylinderMetric 0 z v v / 4 ≤
      N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) z v v := by
    change _ ≤ N.scale⁻¹ ^ 2 * roundCylinderPullback _
      (fun y => N.time_cylinder.forward tau htau (N.coordinate_map y)) z v v
    linarith
  calc
    _ = N.scale ^ 2 * (EvolvingRoundCylinderMetric 0 z v v / 4) := by ring
    _ ≤ N.scale ^ 2 * (N.scale⁻¹ ^ 2 * roundCylinderPullback
        (F.metric (t + tau / (N.scale⁻¹ ^ 2))) (backwardNeckCoordinate N htau) z v v) :=
      mul_le_mul_of_nonneg_left hnormalized (sq_nonneg _)
    _ = _ := by field_simp [N.scale_pos.ne']

include hepsilon hhalf in
private theorem backwardNeck_pullback_horizontal
    (p : UnitTwoSphere) {z : ℝ} (hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v : TangentSpace (𝓡 2) p) :
    roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (v, 0) (v, 0) ≤
      (2 * N.scale) ^ 2 * (roundSphereMetric 2).inner p v v := by
  have h := (abs_le.mp
    (strongNeck_evolving_pullback_quadratic_error N htau (z := (p, z)) hz (v, 0))).2
  have hsphere : 0 ≤ (roundSphereMetric 2).inner p v v := by
    rw [roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner]
    exact real_inner_self_nonneg
  have hc : 2 * (1 - tau) + 72 * epsilon ≤ (4 : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_right hc hsphere
  have hnormalized : N.scale⁻¹ ^ 2 * roundCylinderPullback
      (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (v, 0) (v, 0) ≤
      4 * (roundSphereMetric 2).inner p v v := by
    change N.scale⁻¹ ^ 2 * roundCylinderPullback _ _ (p, z) (v, 0) (v, 0) -
      (2 * (1 - tau) * (roundSphereMetric 2).inner p v v + 0 * 0) ≤
        36 * epsilon * (2 * (1 - 0) * (roundSphereMetric 2).inner p v v + 0 * 0) at h
    change N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric _)
      (fun y => N.time_cylinder.forward tau htau (N.coordinate_map y))
        (p, z) (v, 0) (v, 0) ≤ _
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hnormalized (sq_nonneg N.scale)
  have hcancel : N.scale ^ 2 * (N.scale⁻¹ ^ 2 * roundCylinderPullback
      (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (v, 0) (v, 0)) =
      roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (v, 0) (v, 0) := by
    field_simp [N.scale_pos.ne']
  rw [hcancel] at hmul
  nlinarith

include hepsilon in
private theorem backwardNeck_pullback_axis
    (p : UnitTwoSphere) {z : ℝ} (hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (0, 1) (0, 1) ≤
      (2 * N.scale) ^ 2 := by
  have h := (abs_le.mp
    (strongNeck_evolving_pullback_quadratic_error N htau (z := (p, z)) hz (0, 1))).2
  have hmodel (a : ℝ) : EvolvingRoundCylinderMetric a (p, z) (0, 1) (0, 1) = 1 := by
    simp only [EvolvingRoundCylinderMetric, map_zero, mul_one]
    change 2 * (1 - a) * inner ℝ (0 : EuclideanSpace ℝ (Fin 3)) 0 + 1 = 1
    simp
  rw [hmodel, hmodel] at h
  have hnormalized : N.scale⁻¹ ^ 2 * roundCylinderPullback
      (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (0, 1) (0, 1) ≤ 4 := by
    change N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric _)
      (fun y => N.time_cylinder.forward tau htau (N.coordinate_map y))
        (p, z) (0, 1) (0, 1) ≤ _
    linarith
  have hmul := mul_le_mul_of_nonneg_left hnormalized (sq_nonneg N.scale)
  have hcancel : N.scale ^ 2 * (N.scale⁻¹ ^ 2 * roundCylinderPullback
      (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (0, 1) (0, 1)) =
      roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (backwardNeckCoordinate N htau) (p, z) (0, 1) (0, 1) := by
    field_simp [N.scale_pos.ne']
  rw [hcancel] at hmul
  nlinarith

include hepsilon hhalf in
private theorem backwardNeck_edist_cap (q : UnitTwoSphere) (x : E2) :
    (F.metric (t + tau / (N.scale⁻¹ ^ 2))).edist
      (backwardNeckCoordinate N htau (q, 0))
      (backwardNeckCoordinate N htau ((chartAt E2 q).symm x, 0)) ≤
        ENNReal.ofReal (2 * N.scale * ‖x‖) := by
  let g := F.metric (t + tau / (N.scale⁻¹ ^ 2))
  let Phi := backwardNeckCoordinate N htau
  let c := chartAt E2 q
  let f : E2 → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier :=
    fun y => Phi (c.symm y, 0)
  have hz : (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord (y : E2) : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      Phi (c.symm y, 0) :=
    (backwardNeckCoordinate_smooth N hepsilon htau).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)
  have hf : ContMDiff (𝓡 2) (𝓡 3) 1 f := by
    intro y
    have hs : ContMDiffAt (𝓡 2) (𝓡 3) ∞ f y :=
      (hcoord y).comp y (g := Phi) (f := fun y : E2 => (c.symm y, (0 : ℝ)))
        ((sphere_chart_symm_contMDiff q y).prodMk contMDiffAt_const)
    exact hs.of_le (by simp)
  have hd (y : E2) (v : TangentSpace (𝓡 2) y) :
      mfderiv (𝓡 2) (𝓡 3) f y v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi (c.symm y, 0)
          (mfderiv (𝓡 2) (𝓡 2) c.symm y v, 0) := by
    change mfderiv (𝓡 2) (𝓡 3) (Phi ∘ fun y => (c.symm y, 0)) y v = _
    rw [mfderiv_comp_apply y ((hcoord y).mdifferentiableAt (by simp))
      (((sphere_chart_symm_contMDiff q y).mdifferentiableAt (by simp)).prodMk
        mdifferentiableAt_const)]
    rw [mfderiv_prodMk
      ((sphere_chart_symm_contMDiff q y).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mfderiv_const]
    rfl
  have hbound (y : E2) (v : TangentSpace (𝓡 2) y) :
      g.inner (f y) (mfderiv (𝓡 2) (𝓡 3) f y v)
        (mfderiv (𝓡 2) (𝓡 3) f y v) ≤
      (2 * N.scale) ^ 2 * (RiemannianMetric.euclideanMetric 2).inner y v v := by
    rw [hd]
    have h := backwardNeck_pullback_horizontal N hepsilon htau hhalf (c.symm y) hz
      (mfderiv (𝓡 2) (𝓡 2) c.symm y v)
    have hround := (roundSphere_chart_quadratic_bounds q (x := y) le_rfl v).2
    change (roundSphereMetric 2).inner (c.symm y)
      (mfderiv (𝓡 2) (𝓡 2) c.symm y v) (mfderiv (𝓡 2) (𝓡 2) c.symm y v) ≤ ‖v‖ ^ 2 at hround
    exact h.trans ((mul_le_mul_of_nonneg_left hround (sq_nonneg _)).trans_eq (by
      rw [RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq]))
  have hdist := (RiemannianMetric.euclideanMetric 2).edist_le_mul_of_inner_mfderiv_le
    g hf (mul_pos (by norm_num) N.scale_pos) hbound 0 x
  simpa only [f, c, sphere_chart_symm_zero, RiemannianMetric.euclideanMetric_edist,
    edist_dist, dist_zero_left,
    ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) N.scale_pos.le)] using hdist

include hepsilon in
private theorem backwardNeck_edist_axis (q : UnitTwoSphere) {a b : ℝ}
    (ha : a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (hb : b ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    (F.metric (t + tau / (N.scale⁻¹ ^ 2))).edist
      (backwardNeckCoordinate N htau (q, a)) (backwardNeckCoordinate N htau (q, b)) ≤
        ENNReal.ofReal (2 * N.scale * |b - a|) := by
  have hscale := N.scale_pos
  let g := F.metric (t + tau / (N.scale⁻¹ ^ 2))
  let Phi := backwardNeckCoordinate N htau
  let gamma : ℝ → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier := fun z => Phi (q, z)
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma (Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    (backwardNeckCoordinate_smooth N hepsilon htau).comp
      (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hz => ⟨mem_univ _, hz⟩)
  have hspeed (z : ℝ) (hz : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
      g.tangentNorm (gamma z) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma z 1) ≤ 2 * N.scale := by
    have hcoord : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Phi (q, z) :=
      (backwardNeckCoordinate_smooth N hepsilon htau).contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ q, hz⟩)
    have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma z 1 =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi (q, z) (0, 1) := by
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (Phi ∘ fun z : ℝ => (q, z)) z 1 = _
      rw [mfderiv_comp_apply z (hcoord.mdifferentiableAt (by simp))
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
      simp only [mfderiv_prod_right]
      rfl
    have h := backwardNeck_pullback_axis N hepsilon htau q hz
    unfold RiemannianMetric.tangentNorm
    rw [hd]
    exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (by positivity))
  have hordered {a b : ℝ} (ha : a ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
      (hb : b ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (hab : a ≤ b) :
      g.edist (gamma a) (gamma b) ≤ ENNReal.ofReal (2 * N.scale * (b - a)) := by
    apply g.edist_le_of_tangentNorm_le hab isOpen_Ioo
      (fun z hz => ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩) hgamma (by positivity)
    exact fun z hz => hspeed z ⟨ha.1.trans_le hz.1, hz.2.trans_lt hb.2⟩
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hordered ha hb hab
  · let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) :
        (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier → Type _) := ⟨g.toRiemannianMetric⟩
    have hcomm : g.edist (gamma a) (gamma b) = g.edist (gamma b) (gamma a) :=
      Manifold.riemannianEDist_comm
    change g.edist (gamma a) (gamma b) ≤ _
    rw [hcomm, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact hordered hb ha hba

include hepsilon hhalf in
private theorem backwardNeck_cap_subset_ball (q : UnitTwoSphere) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    backwardNeckCoordinate N htau '' (neckModelCap q a ×ˢ Ioo (-a) a) ⊆
      (F.metric (t + tau / (N.scale⁻¹ ^ 2))).ball
        (backwardNeckCoordinate N htau (q, 0)) (4 * N.scale * a) := by
  have hscale := N.scale_pos
  let g := F.metric (t + tau / (N.scale⁻¹ ^ 2))
  rintro y ⟨⟨p, z⟩, ⟨⟨x, hx, rfl⟩, hz⟩, rfl⟩
  have hxnorm : ‖x‖ < a := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hzabs : |z| < a := abs_lt.mpr hz
  have hinv : (1 : ℝ) < epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (by linarith)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hzN : z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨by linarith [hz.1], hz.2.trans_le (ha1.trans hinv.le)⟩
  have haxis := backwardNeck_edist_axis N hepsilon htau
    ((chartAt E2 q).symm x) hzero hzN
  simp only [sub_zero] at haxis
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) :
      (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier → Type _) := ⟨g.toRiemannianMetric⟩
  change g.edist _ _ < _
  apply (Manifold.riemannianEDist_triangle (y :=
    backwardNeckCoordinate N htau ((chartAt E2 q).symm x, 0))).trans_lt
  apply (add_le_add (backwardNeck_edist_cap N hepsilon htau hhalf q x) haxis).trans_lt
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 4 * N.scale * a)).mpr
  nlinarith [mul_pos N.scale_pos (sub_pos.mpr hxnorm),
    mul_pos N.scale_pos (sub_pos.mpr hzabs)]

private def backwardNeckHomeomorph :
    OpenPartialHomeomorph RoundCylinderSpace (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier := by
  let N0 := spatialNeck N (show epsilon < 1 / 2 by linarith)
  let f := N.time_cylinder.forward tau htau
  let f' := N.time_cylinder.inverse tau htau
  have hinverse : MapsTo f' (f '' N.carrier) N.carrier := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [f, f', N.time_cylinder.left_inverse tau htau hx] using hx
  exact
    { toFun := backwardNeckCoordinate N htau
      invFun := N.coordinate_inverse ∘ f'
      source := univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
      target := f '' N.carrier
      map_source' := fun z hz => ⟨N.coordinate_map z, N0.coordinate_map_mem hz, rfl⟩
      map_target' := fun y hy => ⟨mem_univ _, N.coordinate_inverse_mem _ (hinverse hy)⟩
      left_inv' := by
        intro z hz
        change N.coordinate_inverse (f' (f (N.coordinate_map z))) = z
        have hleft : f' (f (N.coordinate_map z)) = N.coordinate_map z :=
          N.time_cylinder.left_inverse tau htau (N0.coordinate_map_mem hz)
        rw [hleft]
        exact N0.coordinate_inverse_coordinate_map hz
      right_inv' := by
        rintro y ⟨x, hx, rfl⟩
        change f (N.coordinate_map (N.coordinate_inverse (f' (f x)))) = f x
        have hleft : f' (f x) = x := N.time_cylinder.left_inverse tau htau hx
        rw [hleft, N.coordinate_inverse_right x hx]
      open_source := isOpen_univ.prod isOpen_Ioo
      open_target := cylinder_isOpen_forward_image N.time_cylinder N.carrier_open tau htau
      continuousOn_toFun := (backwardNeckCoordinate_smooth N hepsilon htau).continuousOn
      continuousOn_invFun := N.coordinate_inverse_smooth.continuousOn.comp
        (N.time_cylinder.inverse_smooth tau htau).continuousOn hinverse }

private theorem backwardNeckHomeomorph_flat_smooth :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    let e := backwardNeckHomeomorph N hepsilon htau
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let N0 := spatialNeck N (show epsilon < 1 / 2 by linarith)
  constructor
  · exact (N.time_cylinder.forward_smooth tau htau).comp N0.coordinate_map_flat_smooth
      (fun z hz => N0.coordinate_map_mem hz)
  · apply N0.coordinate_inverse_flat_smooth.comp (N.time_cylinder.inverse_smooth tau htau)
    rintro y ⟨x, hx, rfl⟩
    change N.time_cylinder.inverse tau htau (N.time_cylinder.forward tau htau x) ∈ N.carrier
    rw [N.time_cylinder.left_inverse tau htau hx]
    exact hx

include hepsilon in
private theorem backwardNeck_volume_image_lower {A : Set RoundCylinderSpace}
    (hA : MeasurableSet A) (hAD : A ⊆ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ENNReal.ofReal (N.scale / 2) ^ 3 * roundCylinderVolumeMeasure A ≤
      (F.metric (t + tau / (N.scale⁻¹ ^ 2))).volumeMeasure
        (backwardNeckCoordinate N htau '' A) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let g := F.metric (t + tau / (N.scale⁻¹ ^ 2))
  let e := backwardNeckHomeomorph N hepsilon htau
  have hsmooth := backwardNeckHomeomorph_flat_smooth N hepsilon htau
  have hpos : 0 < N.scale / 2 := div_pos N.scale_pos (by norm_num)
  have htangent : ∀ z ∈ e.source, ∀ v : TangentSpace (𝓡 3) z,
      roundCylinderMetric.tangentNorm z v ≤
        (N.scale / 2)⁻¹ * g.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) := by
    intro z hz v
    let d := roundCylinderModelDiffeomorph
    have hcomp := mfderiv_comp z
      (((backwardNeckCoordinate_smooth N hepsilon htau).contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).mdifferentiableAt (by simp))
      (d.symm.contMDiff.mdifferentiable (by simp) z)
    have hpull : g.inner (e z) (mfderiv (𝓡 3) (𝓡 3) e z v)
        (mfderiv (𝓡 3) (𝓡 3) e z v) =
      roundCylinderPullback g (backwardNeckCoordinate N htau) z
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm z v)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm z v) := by
      change mfderiv (𝓡 3) (𝓡 3) e z = _ at hcomp
      change g.inner _ _ _ = g.inner _ _ _
      rw [hcomp]
      rfl
    have h := backwardNeck_pullback_lower N hepsilon htau hz.2
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm z v)
    rw [← roundCylinderMetric_inner_flat z v v, ← hpull] at h
    apply (le_inv_mul_iff₀ hpos).mpr
    unfold RiemannianMetric.tangentNorm
    simpa only [Real.sqrt_mul (sq_nonneg (N.scale / 2)), Real.sqrt_sq hpos.le] using
      Real.sqrt_le_sqrt h
  have hinverse := roundCylinderMetric.inverse_tangentNorm_le_of_le g e
    ⟨hsmooth.1.mdifferentiableOn (by simp), hsmooth.2.mdifferentiableOn (by simp)⟩
    (V := e.source) subset_rfl htangent
  rw [e.image_source_eq_target] at hinverse
  have hv := roundCylinderMetric.volumeMeasure_le_image_of_inverse_tangentNorm_le g e
    (hsmooth.2.of_le (by simp)) (inv_pos.mpr hpos) hinverse hA hAD
  change roundCylinderVolumeMeasure A ≤
    ENNReal.ofReal (N.scale / 2)⁻¹ ^ 3 * g.volumeMeasure (backwardNeckCoordinate N htau '' A) at hv
  calc
    _ ≤ ENNReal.ofReal (N.scale / 2) ^ 3 *
        (ENNReal.ofReal (N.scale / 2)⁻¹ ^ 3 *
          g.volumeMeasure (backwardNeckCoordinate N htau '' A)) := mul_le_mul_right hv _
    _ = _ := by
      rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul hpos.le,
        mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_pow, one_mul]

include hepsilon hhalf in




theorem strongNeck_backward_center_ball_volume {r : ℝ} (hr : 0 < r)
    (hrscale : r ≤ 4 * N.scale) :
    ENNReal.ofReal (neckNoncollapseConstant * r ^ 3) ≤
      calibratedMetricVolume (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        ((F.metric (t + tau / (N.scale⁻¹ ^ 2))).ball
          (N.time_cylinder.forward tau htau N.center) r) := by
  have hscale := N.scale_pos
  have harea := neckModelDiskArea_pos
  let a := r / (4 * N.scale)
  have ha : 0 < a := div_pos hr (mul_pos (by norm_num) N.scale_pos)
  have ha1 : a ≤ 1 := (div_le_one (mul_pos (by norm_num) N.scale_pos)).mpr hrscale
  have har : 4 * N.scale * a = r := by
    dsimp only [a]
    field_simp [N.scale_pos.ne']
  obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hcenter⟩ := N.central_sphere_eq ▸ N.center_on_central_sphere
  have hs0 : s = 0 := hs
  subst s
  let A := neckModelCap q a ×ˢ Ioo (-a) a
  have hA : MeasurableSet A := (neckModelCap_open q a).measurableSet.prod measurableSet_Ioo
  have hinv : (1 : ℝ) < epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (by linarith)
  have hAD : A ⊆ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    rintro ⟨p, z⟩ ⟨_hp, hz⟩
    exact ⟨mem_univ _, by linarith [hz.1], hz.2.trans_le (ha1.trans hinv.le)⟩
  have hAball : backwardNeckCoordinate N htau '' A ⊆
      (F.metric (t + tau / (N.scale⁻¹ ^ 2))).ball
        (N.time_cylinder.forward tau htau N.center) r := by
    simpa only [backwardNeckCoordinate, hcenter, har, A] using
      backwardNeck_cap_subset_ball N hepsilon htau hhalf q ha ha1
  have hline : volume (Ioo (-a) a) = ENNReal.ofReal (2 * a) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hmodel : ENNReal.ofReal (neckModelDiskArea * a ^ 3) ≤
      roundCylinderVolumeMeasure A := by
    rw [roundCylinderVolumeMeasure_eq_prod, Measure.prod_prod, hline]
    have heq : ENNReal.ofReal (neckModelDiskArea * a ^ 3) =
        ENNReal.ofReal (neckModelDiskArea * a ^ 2 / 2) * ENNReal.ofReal (2 * a) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ neckModelDiskArea * a ^ 2 / 2)]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul' (neckModelCap_area_lower q ha ha1) le_rfl
  have heq : ENNReal.ofReal (neckNoncollapseConstant * r ^ 3) =
      ENNReal.ofReal (N.scale / 2) ^ 3 * ENNReal.ofReal (neckModelDiskArea * a ^ 3) := by
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ N.scale / 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N.scale / 2) ^ 3)]
    congr 1
    dsimp only [a, neckNoncollapseConstant]
    field_simp [N.scale_pos.ne']
    ring
  rw [PoincareConjecture.Proofs.M15.calibratedMetricVolume_eq_euclideanHausdorff, heq]
  exact (mul_le_mul' le_rfl hmodel).trans
    ((backwardNeck_volume_image_lower N hepsilon htau hA hAD).trans (measure_mono hAball))

end PoincareConjecture.M32
