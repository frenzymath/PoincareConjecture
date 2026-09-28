import PoincareConjecture.Proofs.M62.Lemma19_6_Orthogonality
import PoincareConjecture.Proofs.M62.Lemma19_6_InteriorRegularity
import PoincareConjecture.Proofs.M62.Cor0_3_Regularization
import Mathlib.Analysis.InnerProductSpace.Basic










set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem hasDerivAt_curvatureSquared_parameter (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    HasDerivAt (m62CurvatureSquared F c t)
      (2 * (F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative (F.connection t) (fun y ↦ c y t)
          (m62CurvatureVector F c t) x)
        (m62CurvatureVector F c t x)) x := by
  have hmem : (x, t) ∈ (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) := ⟨Set.mem_univ _, ht⟩
  have hspace : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun y : ℝ ↦ (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hH := ((((curvature_joint_contMDiff F c hc) (x, t) hmem).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)).mdifferentiableAt (by simp)).comp x hspace
  have hγ := (hc.spatial_regular t (Set.Ioo_subset_Icc_self ht) x).mdifferentiableAt
    (by norm_num)
  have h := hasDerivAt_metric_pairing (F.connection t) (γ := fun y ↦ c y t)
    (Y := m62CurvatureVector F c t) (Z := m62CurvatureVector F c t) hγ hH hH
  apply h.congr_deriv
  rw [(F.metric t).symm (c x t) (m62CurvatureVector F c t x)
    (rampHorizontalCovariantDerivative (F.connection t) (fun y ↦ c y t)
      (m62CurvatureVector F c t) x)]
  ring



theorem regularized_arcDerivative_eq (hc : M62ShrinkingCurve F c)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    m62ArcDerivative F c t (m62RegularizedCurvature F c ε t) x =
      (F.metric t).inner (c x t) (m62SpatialNormalDerivative F c t x)
        (m62CurvatureVector F c t x) / m62RegularizedCurvature F c ε t x := by
  have h := regularized_hasDerivAt_parameter F c hε
    (hasDerivAt_curvatureSquared_parameter F c hc ht x)
  have horth : (F.metric t).inner (c x t) (spatialUnitTangent F c t x)
      (m62CurvatureVector F c t x) = 0 := by
    rw [(F.metric t).symm]
    exact curvature_unitTangent_inner_zero F c hc (Set.Ioo_subset_Icc_self ht) x
  have hh := (regularized_pos F c hε t x).ne'
  have hv := (speed_pos F c hc (Set.Ioo_subset_Icc_self ht) x).ne'
  rw [m62ArcDerivative, h.deriv]
  simp only [m62SpatialNormalDerivative, m62SpatialDerivative, map_sub, sub_apply, map_smul,
    smul_apply, smul_eq_mul, horth, mul_zero, sub_zero]
  field_simp



theorem regularized_gradient_le (hc : M62ShrinkingCurve F c)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    let P := m62SpatialNormalDerivative F c t x
    (m62ArcDerivative F c t (m62RegularizedCurvature F c ε t) x) ^ 2 ≤
      (F.metric t).inner (c x t) P P := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let P := m62SpatialNormalDerivative F c t x
  let H := m62CurvatureVector F c t x
  have hCS : ((F.metric t).inner (c x t) P H) ^ 2 ≤
      (F.metric t).inner (c x t) P P * m62CurvatureSquared F c t x := by
    change (inner ℝ P H) ^ 2 ≤ inner ℝ P P * inner ℝ H H
    simpa only [pow_two] using real_inner_mul_inner_self_le P H
  have hP : 0 ≤ (F.metric t).inner (c x t) P P := by
    change 0 ≤ inner ℝ P P
    exact real_inner_self_nonneg
  have hk : m62CurvatureSquared F c t x ≤ m62RegularizedCurvature F c ε t x ^ 2 := by
    rw [regularized_sq F c ε t x]
    exact le_add_of_nonneg_right (sq_nonneg ε)
  have hbound := hCS.trans (mul_le_mul_of_nonneg_left hk hP)
  rw [regularized_arcDerivative_eq F c hc hε ht x, div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos (regularized_pos F c hε t x))).mpr hbound

end PoincareConjecture.M62
