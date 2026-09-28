import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.CovariantJets
import PoincareConjecture.Proofs.M32.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic



















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

universe u

namespace PoincareConjecture.M32

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem backward_normalized_pullback_quadratic
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (g : RiemannianMetric 3 M)
    (Phi : RoundCylinderSpace → M) {Q epsilon tau : ℝ}
    (hepsilon : 0 < epsilon) (htau : tau ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon tau
      (fun z v w => Q * roundCylinderPullback g Phi z v w))
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (w : RoundCylinderTangent (q, s)) :
    |Q * roundCylinderPullback g Phi (q, s) w w -
        EvolvingRoundCylinderMetric tau (q, s) w w| ≤
      36 * epsilon * EvolvingRoundCylinderMetric 0 (q, s) w w := by
  let D := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi (q, s)
  let P : RoundCylinderTangent (q, s) →ₗ[ℝ] TangentSpace (𝓡 2) q :=
    LinearMap.fst ℝ E2 ℝ
  let A : RoundCylinderTangent (q, s) →ₗ[ℝ]
      RoundCylinderTangent (q, s) →ₗ[ℝ] ℝ :=
    Q • (g.inner (Phi (q, s))).toBilinForm.comp D.toLinearMap D.toLinearMap -
      (roundCylinderProductMetric.inner (q, s)).toBilinForm +
      (2 * tau) • ((roundSphereMetric 2).inner q).toBilinForm.comp P P
  have hA (v v' : RoundCylinderTangent (q, s)) :
      A v v' = Q * roundCylinderPullback g Phi (q, s) v v' -
        EvolvingRoundCylinderMetric tau (q, s) v v' := by
    change Q * roundCylinderPullback g Phi (q, s) v v' -
      roundCylinderProductMetric.inner (q, s) v v' +
        (2 * tau) * (roundSphereMetric 2).inner q v.1 v'.1 = _
    rw [roundCylinderProductMetric_inner]
    simp only [EvolvingRoundCylinderMetric, roundSphereMetric_inner,
      RiemannianMetric.euclideanMetric_inner]
    ring
  let L0 := mfderiv (𝓡 2) (𝓡 2) (chartAt E2 q).symm 0
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let L : E3 →ₗ[ℝ] RoundCylinderTangent (q, s) :=
    ((L0.toLinearMap.comp (LinearMap.fst ℝ E2 ℝ)).prod
      (LinearMap.snd ℝ E2 ℝ)).comp T.toLinearMap
  have hL (v : E3) : L v = (L0 (T v).1, (T v).2) := rfl
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).reindex ((finRotate 3).symm)
  have hb (i : Fin 3) : b i = roundCylinderEuclideanBasis i := by
    rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_toBasis]
    rfl
  have hcoeff (i j : Fin 3) : |(A.compl₁₂ L L) (b i) (b j)| ≤ 4 * epsilon := by
    have h := evolving_covariant_component_center_le hepsilon htau hclose q hs
      (k := 0) (Nat.zero_le _) ![i, j]
    norm_num only [roundCylinderIteratedDerivative, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.add_zero, pow_succ, pow_zero] at h
    simp only [roundCylinderGram, roundCylinderTensorCoefficient] at h
    erw [sphere_chart_symm_zero] at h
    change |A (L (b i)) (L (b j))| ≤ _
    rw [hA, hb, hb, hL, hL]
    simp only [T, lineModelEquiv_symm_roundCylinderEuclideanBasis, L0]
    convert! h using 1
  have hquadratic (v : E3) : |A (L v) (L v)| ≤
      36 * epsilon * roundCylinderEuclideanMetric.inner 0 v v := by
    have h := bilinear_abs_apply_self_le_nine_mul b (A.compl₁₂ L L) hcoeff v
    have hmodel := mul_le_mul_of_nonneg_left
      (roundCylinderEuclideanMetric_norm_sq_le v)
      (show 0 ≤ 36 * epsilon by positivity)
    exact (by simpa only [LinearMap.compl₁₂_apply] using h :
      |A (L v) (L v)| ≤ 9 * (4 * epsilon) * ‖v‖ ^ 2).trans
        (by convert hmodel using 1; ring)
  have hsurj : Function.Surjective L0 := by
    apply LinearMap.surjective_of_injective (f := L0.toLinearMap)
    apply (injective_iff_map_eq_zero L0).mpr
    intro v hv
    have h := roundSphereMetric_chart_symm_inner q 0 v v
    rw [sphere_chart_symm_zero] at h
    change (roundSphereMetric 2).inner q (L0 v) (L0 v) = _ at h
    rw [hv] at h
    norm_num [real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm)
  obtain ⟨v, hv⟩ := hsurj w.1
  let v' := RiemannianMetric.lineModelEquiv 2 (v, w.2)
  have hv' : T v' = (v, w.2) :=
    (RiemannianMetric.lineModelEquiv 2).symm_apply_apply _
  have hLw : L v' = w := by rw [hL, hv', hv, Prod.mk.eta]
  have hsphere : (roundSphereMetric 2).inner q w.1 w.1 = ⟪v, v⟫_ℝ := by
    have h := roundSphereMetric_chart_symm_inner q 0 v v
    rw [sphere_chart_symm_zero] at h
    change (roundSphereMetric 2).inner q (L0 v) (L0 v) = _ at h
    rw [hv] at h
    norm_num only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add, one_mul] at h
    exact h
  have hmodel : roundCylinderEuclideanMetric.inner 0 v' v' =
      EvolvingRoundCylinderMetric 0 (q, s) w w := by
    change roundCylinderModelCoefficients
      ((RiemannianMetric.lineModelEquiv 2).symm 0) (T v') (T v') = _
    rw [map_zero, hv', roundCylinderModelCoefficients_apply]
    change _ = 2 * (1 - 0) * (roundSphereMetric 2).inner q w.1 w.1 + w.2 * w.2
    rw [hsphere]
    norm_num only [Prod.fst_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_add, sub_zero, mul_one]
  have h := hquadratic v'
  rw [hLw, hA, hmodel] at h
  exact h

private theorem backward_coordinate_mem
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    N.coordinate_map z ∈ N.carrier := by
  let w : NeckDomain epsilon := (z.1, ⟨z.2, hz⟩)
  have h := (N.coordinate w).property
  simpa only [N.coordinate_map_eq w, w] using h





theorem strongNeck_evolving_pullback_quadratic_error
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (w : RoundCylinderTangent z) :
    |N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (fun y => N.time_cylinder.forward tau htau (N.coordinate_map y)) z w w -
      EvolvingRoundCylinderMetric tau z w w| ≤
        36 * epsilon * EvolvingRoundCylinderMetric 0 z w w := by
  let Phi : RoundCylinderSpace → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier :=
    fun y => N.time_cylinder.forward tau htau (N.coordinate_map y)
  have hclose : RoundCylinderClose epsilon tau (fun y v v' => N.scale⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2))) Phi y v v') := by
    obtain ⟨hsmooth, bound, hbound, hjet⟩ := N.metric_comparison
    have hstored : RoundCylinderClose epsilon tau
        (generalizedCylinderPullback N.time_cylinder N.coordinate_map tau) :=
      ⟨hsmooth tau htau, bound, hbound, hjet tau htau⟩
    apply roundCylinderClose_congr_axial (hclose := hstored)
    intro y hy v v'
    have hcoord := (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hy⟩)).mdifferentiableAt
        (by simp)
    have hforward := ((N.time_cylinder.forward_smooth tau htau).contMDiffAt
      (N.carrier_open.mem_nhds (backward_coordinate_mem N hy))).mdifferentiableAt
        (by simp)
    simp only [generalizedCylinderPullback, dif_pos htau, GeneralizedFlowCylinder.pullbackInner,
      roundCylinderPullback, Phi]
    erw [mfderiv_comp_apply y hforward hcoord v, mfderiv_comp_apply y hforward hcoord v']
  exact backward_normalized_pullback_quadratic (F.metric _) Phi N.epsilon_pos
    ⟨htau.1.le, htau.2⟩ hclose z.1 hz w

end PoincareConjecture.M32
