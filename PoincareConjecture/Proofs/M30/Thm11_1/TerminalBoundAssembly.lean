import PoincareConjecture.Proofs.M30.Thm11_1.FiniteLocalNullSections
import PoincareConjecture.Proofs.M30.Thm11_1.NullNeckBound
import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Scale
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity










set_option autoImplicit false

open Set Manifold PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u v w

namespace PoincareConjecture.M30



theorem exists_related_neck_of_static_canonical
    {M : Type v} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {epsilon C : ℝ} {x : M}
    (hcanonical :
      (∃ N : EpsilonNeck g, N.epsilon = epsilon ∧ N.center = x) ∨
      (∃ K : CapCertificate g,
        K.epsilon = epsilon ∧ K.cap_constant ≤ C ∧ x ∈ K.carrier)) :
    ∃ N : EpsilonNeck g, N.epsilon = epsilon ∧
      D.scalarCurvature x ≤ max 1 C * D.scalarCurvature N.center := by
  rcases hcanonical with ⟨N, hN, rfl⟩ | ⟨K, hK, hKC, hxK⟩
  · refine ⟨N, hN, ?_⟩
    have hpos : 0 < D.scalarCurvature N.center := by
      rw [D.scalarCurvature_eq N.connection]
      exact N.scalar_center_pos
    exact (one_mul _).symm.trans_le
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
  · have hz : K.end_neck.center ∈ K.carrier :=
      K.end_neck_subset
        (K.end_neck.central_sphere_subset K.end_neck.center_on_central_sphere)
    have hzpos : 0 < D.scalarCurvature K.end_neck.center := by
      rw [D.scalarCurvature_eq K.connection]
      exact K.scalar_pos _ hz
    obtain ⟨b, hb, hratio⟩ := K.scalar_ratio
    have hratio' := hratio K.end_neck.center hz x hxK
    rw [K.connection.scalarCurvature_eq D x,
      K.connection.scalarCurvature_eq D K.end_neck.center] at hratio'
    exact ⟨K.end_neck, K.end_neck_epsilon.trans hK,
      hratio'.trans (mul_le_mul_of_nonneg_right
        ((hb.le.trans hKC).trans (le_max_right _ _)) hzpos.le)⟩




theorem exists_terminal_curvature_bound_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {ι : Type w} {N : ι → Type u} {M : Type v}
        [∀ i, TopologicalSpace (N i)] [TopologicalSpace M]
        [∀ i, T2Space (N i)] [∀ i, ConnectedSpace (N i)]
        [T3Space M] [ConnectedSpace M]
        [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N i)]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [∀ i, IsManifold (𝓡 3) ∞ (N i)] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M],
      ∀ (_hC : RicciFlowCurvatureTheory.{u})
        (a : ι → ℝ) (_ha : ∀ i, a i < 0)
        (F : ∀ i, RicciFlow 3 (N i) (Icc (a i) 0)),
        (∀ i, ∀ t ∈ Icc (a i) 0, ∀ z : N i,
          ((F i).connection t).NonnegativeCurvatureOperator z) →
      ∀ {g : RiemannianMetric 3 M} (D : LeviCivitaData g),
        D.CurvatureTensorCalculus → MetricComplete g →
        D.NonnegativeSectionalCurvature →
      ∀ (e : ∀ i, N i → M),
        (∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i)) →
        (∀ i, ∀ z : N i, ∀ v1 v2 : TangentSpace (𝓡 3) z,
          ((F i).metric 0).inner z v1 v2 = g.inner (e i z)
            (mfderiv (𝓡 3) (𝓡 3) (e i) z v1)
            (mfderiv (𝓡 3) (𝓡 3) (e i) z v2)) →
      ∀ p0 : M, D.curvatureTensorNorm p0 ≠ 0 →
        (∀ x y : M, ∃ i, x ∈ range (e i) ∧ p0 ∈ range (e i) ∧ y ∈ range (e i)) →
      ∀ epsilon C : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
        (∀ x : M, 4 < D.scalarCurvature x →
          (∃ N : EpsilonNeck g, N.epsilon = epsilon ∧
            D.scalarCurvature x ≤ max 1 C * D.scalarCurvature N.center) ∨
            IsCompact (univ : Set M)) →
        ∃ B : ℝ, 4 ≤ B ∧ (∀ x : M, D.scalarCurvature x ≤ B) ∧
          ∀ x : M, |D.curvatureTensorNorm x| ≤ 13 * B := by
  classical
  obtain ⟨epsilonPos, hpos, _, hpositive⟩ :=
    RiemannianMetric.exists_universal_neck_scale_lower_bound.{v}
  obtain ⟨epsilonNull, hnull, hsmall, hnullBound⟩ :=
    exists_neck_scalar_and_curvature_bound_of_local_parallel_null_sections.{v}
  refine ⟨min epsilonPos epsilonNull, lt_min hpos hnull,
    (min_le_right _ _).trans hsmall, ?_⟩
  intro ι N M _ _ _ _ _ _ _ _ _ _ _ _ hC a ha F hoperator
    g D hD hcomplete hsec e he hmetric p0 hnonflat hcapture epsilon C hepsilon hle hcanonical
  let : Nonempty M := ⟨p0⟩
  have hscalar : ∃ B : ℝ, 4 ≤ B ∧ ∀ x : M, D.scalarCurvature x ≤ B := by
    by_cases hcompact : IsCompact (univ : Set M)
    · obtain ⟨B, hB⟩ := hcompact.bddAbove_image
        hD.contMDiff_scalarCurvature.continuous.continuousOn
      exact ⟨max 4 B, le_max_left _ _, fun x =>
        (hB (mem_image_of_mem _ (mem_univ x))).trans (le_max_right _ _)⟩
    have hcanonical' (x : M) (hx : 4 < D.scalarCurvature x) :
        ∃ N : EpsilonNeck g, N.epsilon = epsilon ∧
          D.scalarCurvature x ≤ max 1 C * D.scalarCurvature N.center :=
      (hcanonical x hx).resolve_right hcompact
    by_cases hpositive' : D.StrictlyPositiveSectionalCurvature
    · obtain ⟨rho, hrho, hfloor⟩ := hpositive M g D hcomplete hpositive'
        epsilon hepsilon (hle.trans (min_le_left _ _))
      refine ⟨max 4 (max 1 C * rho ^ (-2 : ℝ)), le_max_left _ _, ?_⟩
      intro x
      by_cases hx : 4 < D.scalarCurvature x
      · obtain ⟨N, hN, hratio⟩ := hcanonical' x hx
        have hcenter : 0 < D.scalarCurvature N.center := by
          rw [D.scalarCurvature_eq N.connection]
          exact N.scalar_center_pos
        have hscale : N.scale = D.scalarCurvature N.center ^ (-1 / 2 : ℝ) := by
          rw [D.scalarCurvature_eq N.connection]
          exact N.scale_eq_scalar
        have hneck : D.scalarCurvature N.center ≤ rho ^ (-2 : ℝ) := by
          calc
            D.scalarCurvature N.center = N.scale ^ (-2 : ℝ) := by
              rw [hscale, ← Real.rpow_mul hcenter.le]
              norm_num
            _ ≤ rho ^ (-2 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos hrho (hfloor N hN) (by norm_num)
        exact (hratio.trans (mul_le_mul_of_nonneg_left hneck
          (zero_le_one.trans (le_max_left _ _)))).trans (le_max_right _ _)
      · exact (le_of_not_gt hx).trans (le_max_left _ _)
    by_cases hlow : ∀ x : M, D.scalarCurvature x ≤ 4
    · exact ⟨4, le_rfl, hlow⟩
    push Not at hlow
    obtain ⟨q, hq⟩ := hlow
    obtain ⟨neck, hneck, _⟩ := hcanonical' q hq
    unfold LeviCivitaData.StrictlyPositiveSectionalCurvature at hpositive'
    push Not at hpositive'
    obtain ⟨x, v1, v2, hv1, hv2, horth, hzero⟩ := hpositive'
    have hzero' : D.curvatureTensor x v1 v2 v1 v2 = 0 := by
      have hle' : D.curvatureTensor x v1 v2 v1 v2 ≤ 0 := by
        simpa only [LeviCivitaData.sectionalCurvature, hv1, hv2, horth,
          one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using hzero
      exact le_antisymm hle' (hsec x v1 v2)
    obtain ⟨hdim, hlocal⟩ := terminal_nullity_and_local_parallel_sections
      hC a ha F hoperator D e he hmetric p0 hnonflat x v1 v2 hv1 hv2 horth hzero'
      (hcapture x)
    obtain ⟨B, _, hB, _⟩ := hnullBound D hD hcomplete hsec hdim hlocal neck
      (hneck ▸ hle.trans (min_le_right _ _))
    exact ⟨max 4 B, le_max_left _ _, fun y =>
      ((le_abs_self _).trans (hB y)).trans (le_max_right _ _)⟩
  obtain ⟨B, hB, hscalar⟩ := hscalar
  refine ⟨B, hB, hscalar, ?_⟩
  intro x
  have hleast : 0 ≤ D.leastSectionalCurvature x := by
    apply Real.sInf_nonneg
    rintro k ⟨v1, v2, _, rfl⟩
    exact hsec x v1 v2
  have hdefect : D.negativeCurvaturePart x = 0 := max_eq_right (neg_nonpos.mpr hleast)
  apply curvatureTensorNorm_le_of_scalar_negativeDefect_le D hD x (by linarith)
    (hscalar x)
  rw [hdefect]
  linarith

end PoincareConjecture.M30
