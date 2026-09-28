import PoincareConjecture.Proofs.M35.CapGeometry.NeckInnerBall
import PoincareConjecture.Proofs.M35.CapGeometry.NeckTipExclusion
import PoincareConjecture.Proofs.M35.CapGeometry.InitialAxialPatch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M35

theorem exists_initial_neck_margin (A epsilon : ℝ) (hA : 0 ≤ A)
    (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ d : ℝ, 0 < d → d ≤ delta →
      ∀ (g : RiemannianMetric 3 StandardCapSpace) (_D : LeviCivitaData g),
        (∀ B : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
          ∀ x u v : StandardCapSpace,
            g.inner (standardRotation B x)
              (mfderiv (𝓡 3) (𝓡 3) (standardRotation B) x u)
              (mfderiv (𝓡 3) (𝓡 3) (standardRotation B) x v) = g.inner x u v) →
        ∀ (x : StandardCapSpace) (N : StandardCylinderPatch d⁻¹ x),
          RoundCylinderClose d 0 (roundCylinderPullback g N.coordinate) →
          ∀ c : ℝ, ∀ hc : 0 < c, c < 2 →
            ∃ hcl : c * epsilon⁻¹ ≤ d⁻¹,
              (∀ y ∈ (N.axialRescale c epsilon⁻¹ hc (inv_pos.mpr he) hcl).carrier,
                A + 5 < (g.edist 0 y).toReal) ∧
              Disjoint (N.axialRescale c epsilon⁻¹ hc (inv_pos.mpr he) hcl).carrier
                {y | g.edist 0 y ≤ ENNReal.ofReal (A + 4)} := by
  obtain ⟨dtip, hdtip, htip⟩ := exists_cylinder_tip_exclusion
  let K := 4 * (A + epsilon⁻¹ + 6)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨min dtip (min (1 / 24) K⁻¹),
    lt_min hdtip (lt_min (by norm_num) (inv_pos.mpr hK)), ?_⟩
  intro d hd hdd g D hrotation x N hclose c hc hc2
  have hdsmall : d ≤ 1 / 24 :=
    hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdK : d ≤ K⁻¹ :=
    hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlong : K ≤ d⁻¹ := by
    simpa only [inv_inv] using inv_anti₀ hd hdK
  have heinv : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hroom : A + 5 < (d⁻¹ / 2 - 2 * epsilon⁻¹) / 2 := by
    dsimp [K] at hlong
    linarith only [hlong]
  have hL : 2 * epsilon⁻¹ < d⁻¹ / 2 := by linarith only [hroom, hA]
  have hcL : c * epsilon⁻¹ < 2 * epsilon⁻¹ := mul_lt_mul_of_pos_right hc2 heinv
  have hcl : c * epsilon⁻¹ ≤ d⁻¹ :=
    (hcL.trans hL).le.trans (half_le_self (inv_pos.mpr hd).le)
  have hexcluded := htip d hd (hdd.trans (min_le_left _ _)) g D hrotation x N hclose
  have hmargin : ∀ y ∈
      (N.axialRescale c epsilon⁻¹ hc (inv_pos.mpr he) hcl).carrier,
      A + 5 < (g.edist 0 y).toReal := by
    intro y hy
    rw [N.axialRescale_carrier] at hy
    have hyax : |(N.inverse y).2| ≤ 2 * epsilon⁻¹ :=
      ((abs_lt.mpr hy.2.2).trans hcL).le
    have hball := N.inner_slab_ball_subset_carrier g hd hdsmall
      (show (0 : ℝ) ∈ Icc (-1) 0 by constructor <;> norm_num)
      hL (half_lt_self (inv_pos.mpr hd)) hclose hy.1 hyax
    have hnot : ¬g.edist y 0 < ENNReal.ofReal ((d⁻¹ / 2 - 2 * epsilon⁻¹) / 2) :=
      fun h => hexcluded (hball h)
    have hsymm : g.edist y 0 = g.edist 0 y :=
      @edist_comm StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace y 0
    rw [hsymm] at hnot
    exact hroom.trans_le
      ((ENNReal.ofReal_le_iff_le_toReal (g.edist_ne_top 0 y)).mp (le_of_not_gt hnot))
  refine ⟨hcl, hmargin, disjoint_left.mpr ?_⟩
  intro y hy hclosed
  have hclosed' : (g.edist 0 y).toReal ≤ A + 4 := by
    exact (ENNReal.toReal_le_toReal (g.edist_ne_top 0 y) ENNReal.ofReal_ne_top).mpr
      hclosed |>.trans_eq (ENNReal.toReal_ofReal (by linarith only [hA]))
  have hm := hmargin y hy
  linarith only [hclosed', hm]

end PoincareConjecture.M35
