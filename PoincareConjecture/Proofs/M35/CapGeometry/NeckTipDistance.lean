import PoincareConjecture.Proofs.M35.CapGeometry.NeckTipExclusion
import PoincareConjecture.Proofs.M35.CapGeometry.NeckBufferedBall
import PoincareConjecture.Proofs.M35.CapGeometry.RadialDerivativeBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M35

open Uniqueness

theorem neck_center_tip_distance_of_exclusion
    {epsilon : ℝ} {x : StandardCapSpace} (N : StandardCylinderPatch epsilon⁻¹ x)
    (g : RiemannianMetric 3 StandardCapSpace) (he : 0 < epsilon)
    (hesmall : epsilon ≤ 1 / 24)
    (hclose : RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate))
    (htip : (0 : StandardCapSpace) ∉ N.carrier) :
    epsilon⁻¹ / 4 ≤ (g.edist 0 x).toReal := by
  have hlength : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hball := N.center_ball_subset_carrier_of_axial_cutoff g he hesmall
    (show (0 : ℝ) ∈ Icc (-1) 0 by constructor <;> norm_num)
    (half_pos hlength) (half_lt_self hlength) hclose
  have hnot : ¬g.edist x 0 < ENNReal.ofReal (epsilon⁻¹ / 4) := by
    intro h
    apply htip
    apply hball
    change g.edist x 0 < ENNReal.ofReal (epsilon⁻¹ / 2 / 2)
    convert h using 2
    ring
  have hsymm : g.edist x 0 = g.edist 0 x :=
    @edist_comm StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace x 0
  rw [hsymm] at hnot
  exact (ENNReal.ofReal_le_iff_le_toReal (g.edist_ne_top 0 x)).mp (le_of_not_gt hnot)

theorem exists_static_neck_tip_distance_threshold :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (atlas : StandardCylinderAtlas) (g : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g),
        (∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
          ∀ x u v : StandardCapSpace,
            g.inner (standardRotation A x)
              (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
              (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v) →
        ∀ N : StandardStaticNeck atlas g D epsilon,
          epsilon⁻¹ / 4 ≤ (g.edist 0 N.center).toReal *
            Real.sqrt (D.scalarCurvature N.center) := by
  obtain ⟨delta, hdelta, htip⟩ := exists_cylinder_tip_exclusion
  refine ⟨min delta (1 / 24), lt_min hdelta (by norm_num), ?_⟩
  intro epsilon he hesmall atlas g D hrotation N
  let Q := D.scalarCurvature N.center
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g Q N.scalar_pos
  let DG := M13.scaleLeviCivitaData D Q N.scalar_pos
  have hclose : RoundCylinderClose epsilon 0 (roundCylinderPullback G N.patch.coordinate) :=
    N.close
  have hexcluded := htip epsilon he (hesmall.trans (min_le_left _ _)) G DG
    (scaleSmoothMetric_rotation_invariant hrotation Q N.scalar_pos) N.center N.patch hclose
  have hd := neck_center_tip_distance_of_exclusion N.patch G he
    (hesmall.trans (min_le_right _ _)) hclose hexcluded
  have hscale := M13.homothety_edist g G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q N.scalar_pos
    (M13.identity_metricHomothety g Q N.scalar_pos) 0 N.center
  change G.edist 0 N.center = _ at hscale
  rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hd
  simpa only [mul_comm] using hd

end PoincareConjecture.M35
