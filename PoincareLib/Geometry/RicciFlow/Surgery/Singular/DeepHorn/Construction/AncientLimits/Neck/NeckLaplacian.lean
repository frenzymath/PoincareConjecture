import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Scalar.ScalarScaling
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Scalar.ScalarLaplacianControl
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Neck.NeckFourJetRealization
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Neck.ScalarControl

/-!
# The actual scalar Laplacian at a sufficiently small neck center

Morgan--Tian Definition 2.18, printed p. 31, equation (3.7), p. 41,
Definition 9.78, p. 232, and Claim 11.35, pp. 289-291. The realized
normalized coefficient germ is a local homothety of the actual metric.
Four-jet continuity and exact center normalization then control its
retained scalar Laplacian with one accuracy threshold.

The eligible templates are EpsilonNeck.normalized_realization_curvature
in Neck/Curvature/Ambient and exists_ambient_curvature_control in
Neck/Curvature/Control. The additional Laplacian scaling is the owned
ScalarScaling proof, re-derived from the exact M34 donor names recorded
there. Derivation: `claim11_35-neck-scalar-evolution.md`, section 3.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M32

/-- The realized normalized neck germ has the actual fourth-power
scalar-Laplacian scale. Source: Definition 2.18, p. 31, equation (3.7),
p. 41, and Claim 11.35, printed pp. 289-291. -/
theorem normalized_neck_realization_scalarLaplacian
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (D : LeviCivitaData g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (Dh : LeviCivitaData h)
    (heq : h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) :
    Dh.laplacian Dh.scalarCurvature 0 =
      N.scale ^ 4 * D.laplacian D.scalarCurvature (N.coordinate_map (q, s)) := by
  let f := N.centeredEuclideanParametrization q s
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add (RiemannianMetric.lineModelEquiv 2).symm.continuous))
  have hzero : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hs
  obtain ⟨V, hV, hVo, hzeroV⟩ := mem_nhds_iff.mp (heq.and (hU.mem_nhds hzero))
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V := fun x hx =>
    (N.centeredEuclideanParametrization_contMDiffAt q s (hV hx).2).contMDiffWithinAt
  have hmetric : ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner x v w = N.scale⁻¹ ^ 2 * g.inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    intro x hx v w
    change h.euclideanCoefficients x v w = _
    rw [(hV hx).1]
    exact N.normalizedEuclideanCoefficients_eq_pullback q s (hV hx).2 v w
  have hc : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hlap := scalarLaplacian_eq_of_local_homothety Dh D hc hVo hf hmetric hzeroV
  simpa only [f, EpsilonNeck.centeredEuclideanParametrization_zero,
    div_eq_mul_inv, inv_pow, inv_inv, ← pow_mul, mul_comm] using hlap

/-- One accuracy threshold bounds the actual scalar Laplacian at every
spatial neck center. Source: Definition 2.18, p. 31, equation (3.7),
p. 41, and Claim 11.35, printed pp. 289-291. -/
theorem exists_neck_center_scalarLaplacian_bound :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M}, ∀ N : EpsilonNeck g, N.epsilon ≤ epsilon₀ →
          |N.connection.laplacian N.connection.scalarCurvature N.center| ≤
            (N.connection.scalarCurvature N.center) ^ 2 / 6 := by
  let D0 := roundCylinderEuclideanMetric.leviCivitaData
  have hmodelScalar : D0.scalarCurvature = fun _ => (1 : ℝ) :=
    funext fun x => roundCylinderEuclideanMetric_scalarCurvature D0 x
  have hmodel : D0.laplacian D0.scalarCurvature 0 = 0 := by
    rw [hmodelScalar]
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    exists_scalar_laplacian_control_of_metric_fourJet D0 0 (by norm_num : (0 : ℝ) < 1 / 6)
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hjets⟩ :=
    exists_normalizedEuclideanCoefficients_realization_fourJet_control.{u} hdelta
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N hN
  have hcenter := N.center_on_central_sphere
  rw [N.central_sphere_eq] at hcenter
  obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hcenter⟩ := hcenter
  have hs0 : s = 0 := hs
  subst s
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have hpos := inv_pos.mpr N.epsilon_pos
    constructor <;> linarith
  obtain ⟨h, Dh, heq, hclose⟩ := hjets N hN q hzero
  have hbound := hcontrol h Dh hclose
  rw [hmodel, sub_zero,
    normalized_neck_realization_scalarLaplacian N N.connection q hzero Dh heq,
    hcenter] at hbound
  have hscale : 0 < N.scale ^ 4 := pow_pos N.scale_pos 4
  rw [abs_mul, abs_of_pos hscale] at hbound
  have hnorm : N.scale ^ 4 * (N.connection.scalarCurvature N.center) ^ 2 = 1 := by
    have hsq := congrArg (fun r : ℝ => r ^ 2) (neckScale_sq_mul_scalar_center N)
    simpa only [mul_pow, ← pow_mul, one_pow] using hsq
  apply (mul_le_mul_iff_right₀ hscale).mp
  rw [← mul_div_assoc, hnorm]
  exact hbound.le

/-- Spatial extraction transfers the common Laplacian threshold to the
actual generalized-flow connection at a strong neck center. Source:
Definition 9.78, p. 232, and Claim 11.35, printed pp. 289-291. -/
theorem exists_strongNeck_center_scalarLaplacian_bound :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilon₀ →
          |(F.connection t).laplacian (F.connection t).scalarCurvature N.center| ≤
            ((F.connection t).scalarCurvature N.center) ^ 2 / 6 := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ := exists_neck_center_scalarLaplacian_bound.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F t epsilon N hepsilon
  have hhalf : epsilon < 1 / 2 := hepsilon.trans_lt (hsmall.trans_lt (by norm_num))
  exact hcontrol (spatialNeck N hhalf) hepsilon

end PoincareMT.M32
