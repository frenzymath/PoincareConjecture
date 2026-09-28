import PoincareConjecture.Proofs.M47.CanonicalNeckTipExclusion
import PoincareConjecture.Proofs.M47.CanonicalNeckCalibratedBall
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M13.Length
import PoincareConjecture.Proofs.M34.Standard.NeckRestriction
import PoincareConjecture.Definitions.M34StandardCapExistence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.Proofs.M47


theorem standardNeck_tip_distance_calibrated
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {epsilon : ℝ} (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200)
    {x : StandardCapSpace} (N : StandardCylinderPatch epsilon⁻¹ x)
    (hclose : RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate)) :
    (19 / 20 : ℝ) * epsilon⁻¹ ≤ (g.edist 0 x).toReal := by
  have htip := standardNeck_tip_not_mem g D hrotation he hsmall N hclose
  have hball := standardNeck_center_ball_subset_calibrated N g he hsmall
    (show (0 : ℝ) ∈ Icc (-1) 0 by constructor <;> norm_num) hclose
  have hnot : ¬g.edist x 0 < ENNReal.ofReal ((19 / 20 : ℝ) * epsilon⁻¹) :=
    fun h => htip (hball h)
  have hsymm : g.edist x 0 = g.edist 0 x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_comm
  rw [hsymm] at hnot
  exact (ENNReal.ofReal_le_iff_le_toReal (g.edist_ne_top 0 x)).mp (le_of_not_gt hnot)



theorem standardStaticNeck_tip_distance_calibrated
    (A : StandardCylinderAtlas) (g : RiemannianMetric 3 StandardCapSpace)
    (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {epsilon : ℝ} (N : StandardStaticNeck A g D epsilon)
    (hsmall : epsilon ≤ 1 / 1200) :
    (19 / 20 : ℝ) * epsilon⁻¹ ≤
      (g.edist 0 N.center).toReal * Real.sqrt (D.scalarCurvature N.center) := by
  let Q := D.scalarCurvature N.center
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g Q N.scalar_pos
  let DG := M13.scaleLeviCivitaData D Q N.scalar_pos
  have hclose : RoundCylinderClose epsilon 0 (roundCylinderPullback G N.patch.coordinate) :=
    N.close
  have hrot : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v := by
    intro A x u v
    change Q * g.inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = Q * g.inner x u v
    rw [hrotation A x u v]
  have hd := standardNeck_tip_distance_calibrated G DG hrot
    N.epsilon_pos hsmall N.patch hclose
  have hscale := M13.homothety_edist g G (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞)
    Q N.scalar_pos (M13.identity_metricHomothety g Q N.scalar_pos) 0 N.center
  change G.edist 0 N.center = _ at hscale
  rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hd
  simpa only [mul_comm] using hd



theorem standardEvolvingNeck_tip_distance_calibrated
    {g0 : StandardInitialMetric} (E : RepairedStandardCapExistenceData g0)
    {t epsilon : ℝ} {x : StandardCapSpace} {I : Set ℝ}
    (N : StandardEvolvingNeck E.atlas E.flow t epsilon x I)
    (hsmall : epsilon ≤ 1 / 1200) (hzero : (0 : ℝ) ∈ I) :
    (19 / 20 : ℝ) * epsilon⁻¹ ≤
      ((E.flow.metric t).edist 0 x).toReal *
        Real.sqrt ((E.flow.connection t).scalarCurvature x) := by
  let N0 : StandardStaticNeck E.atlas (E.flow.metric t) (E.flow.connection t) epsilon := {
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    center := x
    scalar_pos := N.scalar_pos
    patch := N.patch
    close := by
      have h := N.close.at_time hzero
      unfold StandardSpatialCylinderClose
      simpa only [zero_div, add_zero] using h }
  exact standardStaticNeck_tip_distance_calibrated E.atlas (E.flow.metric t)
    (E.flow.connection t) (E.rotation_invariant t N.time_mem) N0 hsmall



theorem standardCanonical_cap_of_tip_distance
    {g0 : StandardInitialMetric} (E : RepairedStandardCapExistenceData g0)
    {t epsilon C : ℝ} {x : StandardCapSpace}
    (hsmall : epsilon ≤ 1 / 1200)
    (hcanonical : StandardCanonicalAlternative E.atlas E.flow t x epsilon C)
    (hdistance : ((E.flow.metric t).edist 0 x).toReal *
      Real.sqrt ((E.flow.connection t).scalarCurvature x) < (19 / 20 : ℝ) * epsilon⁻¹) :
    Nonempty (StandardCapNeighborhood E.atlas E.flow t epsilon C x) := by
  cases hcanonical with
  | cap N => exact ⟨N⟩
  | initial_neck N _ =>
    have hzero : (0 : ℝ) ∈ Icc (-t * (E.flow.connection t).scalarCurvature x) 0 :=
      ⟨mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr N.time_mem.1) N.scalar_pos.le, le_rfl⟩
    exact False.elim ((not_lt_of_ge
      (standardEvolvingNeck_tip_distance_calibrated E N hsmall hzero)) hdistance)
  | evolving_neck N =>
    have hzero : (0 : ℝ) ∈ Ioc (-(1 + epsilon)) 0 := by
      constructor
      · linarith only [N.epsilon_pos]
      · exact le_rfl
    exact False.elim ((not_lt_of_ge
      (standardEvolvingNeck_tip_distance_calibrated E N hsmall hzero)) hdistance)

end PoincareConjecture.Proofs.M47
