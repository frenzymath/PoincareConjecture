import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Scale
import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.M30.Thm5_33.CurvatureNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30





theorem scalar_le_of_neck_cap_scale_floor
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (epsilon C rho : ℝ) (hrho : 0 < rho)
    (hfloor : ∀ N : EpsilonNeck g, N.epsilon = epsilon → rho ≤ N.scale)
    (hcanonical : ∀ x : M, 4 < D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.epsilon = epsilon ∧ N.center = x) ∨
      (∃ K : CapCertificate g,
        K.epsilon = epsilon ∧ K.cap_constant ≤ C ∧ x ∈ K.carrier)) :
    ∀ x : M, D.scalarCurvature x ≤ max 4 (max 1 C * rho ^ (-2 : ℝ)) := by
  have hpow : 0 ≤ rho ^ (-2 : ℝ) := (Real.rpow_pos_of_pos hrho _).le
  have hmax : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  have hneck (N : EpsilonNeck g) (hN : N.epsilon = epsilon) :
      D.scalarCurvature N.center ≤ rho ^ (-2 : ℝ) := by
    have hscalar : 0 < D.scalarCurvature N.center := by
      rw [D.scalarCurvature_eq N.connection]
      exact N.scalar_center_pos
    have hscale : N.scale = D.scalarCurvature N.center ^ (-1 / 2 : ℝ) := by
      rw [D.scalarCurvature_eq N.connection]
      exact N.scale_eq_scalar
    calc
      D.scalarCurvature N.center = N.scale ^ (-2 : ℝ) := by
        rw [hscale, ← Real.rpow_mul hscalar.le]
        norm_num
      _ ≤ rho ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hrho (hfloor N hN) (by norm_num)
  intro x
  by_cases hx : 4 < D.scalarCurvature x
  · rcases hcanonical x hx with ⟨N, hN, hcenter⟩ | ⟨K, hK, hKC, hxK⟩
    · calc
        D.scalarCurvature x ≤ rho ^ (-2 : ℝ) := hcenter ▸ hneck N hN
        _ ≤ max 1 C * rho ^ (-2 : ℝ) :=
          (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
        _ ≤ max 4 (max 1 C * rho ^ (-2 : ℝ)) := le_max_right _ _
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
      calc
        D.scalarCurvature x ≤ b * D.scalarCurvature K.end_neck.center := hratio'
        _ ≤ max 1 C * D.scalarCurvature K.end_neck.center :=
          mul_le_mul_of_nonneg_right
            ((hb.le.trans hKC).trans (le_max_right _ _)) hzpos.le
        _ ≤ max 1 C * rho ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left
          (hneck K.end_neck (K.end_neck_epsilon.trans hK)) hmax
        _ ≤ max 4 (max 1 C * rho ^ (-2 : ℝ)) := le_max_right _ _
  · exact (le_of_not_gt hx).trans (le_max_left _ _)




theorem exists_positive_neck_cap_curvature_bound_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 < 1 / 2 ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [ConnectedSpace M] [Nonempty M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M],
      ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
        D.CurvatureTensorCalculus → MetricComplete g →
        D.StrictlyPositiveSectionalCurvature →
      ∀ epsilon C : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
        (∀ x : M, 4 < D.scalarCurvature x →
          (∃ N : EpsilonNeck g, N.epsilon = epsilon ∧ N.center = x) ∨
          (∃ K : CapCertificate g,
            K.epsilon = epsilon ∧ K.cap_constant ≤ C ∧ x ∈ K.carrier)) →
        ∃ B : ℝ, 4 ≤ B ∧ (∀ x : M, D.scalarCurvature x ≤ B) ∧
          ∀ x : M, |D.curvatureTensorNorm x| ≤ 13 * B := by
  classical
  obtain ⟨epsilon0, hepsilon0, hsmall, hfloor⟩ :=
    RiemannianMetric.exists_universal_neck_scale_lower_bound.{u}
  refine ⟨epsilon0, hepsilon0, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D hD hcomplete hpositive epsilon C hepsilon hsmall' hcanonical
  obtain ⟨rho, hrho, hscale⟩ := hfloor M g D hcomplete hpositive epsilon hepsilon hsmall'
  let B := max 4 (max 1 C * rho ^ (-2 : ℝ))
  have hB : 4 ≤ B := le_max_left _ _
  have hscalar : ∀ x : M, D.scalarCurvature x ≤ B :=
    scalar_le_of_neck_cap_scale_floor D epsilon C rho hrho hscale hcanonical
  refine ⟨B, hB, hscalar, ?_⟩
  intro x
  have hleast : 0 ≤ D.leastSectionalCurvature x := by
    let E : Set ℝ := {k | ∃ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w ∧ k = D.curvatureTensor x v w v w}
    change 0 ≤ sInf E
    by_cases hE : E.Nonempty
    · apply le_csInf hE
      rintro k ⟨v, w, hvw, rfl⟩
      have hsec := hpositive x v w hvw.1 hvw.2.1 hvw.2.2
      simpa only [LeviCivitaData.sectionalCurvature, hvw.1, hvw.2.1, hvw.2.2,
        one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using hsec.le
    · rw [Set.not_nonempty_iff_eq_empty.mp hE, Real.sInf_empty]
  have hdefect : D.negativeCurvaturePart x = 0 :=
    max_eq_right (neg_nonpos.mpr hleast)
  apply curvatureTensorNorm_le_of_scalar_negativeDefect_le D hD x (by linarith)
    (hscalar x)
  rw [hdefect]
  linarith

end PoincareConjecture.M30
