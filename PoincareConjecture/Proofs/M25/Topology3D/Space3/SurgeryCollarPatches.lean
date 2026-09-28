import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import Mathlib.Analysis.Normed.Module.Convex











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem surgery_collar_patch_geometry {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1 / 4) :
    let H := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2
    let X := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).1
    let V : Fin 2 → Set UnitTwoSphere := ![{p | -beta < H p}, {p | H p < -31 / 32}]
    let K : Fin 2 → Set UnitTwoSphere :=
      ![{p | 0 ≤ H p}, {p | H p ≤ 0 ∧ ‖X p‖ ≤ 1 / 8}]
    (∀ i, IsOpen (V i)) ∧ (∀ i, IsPreconnected (V i)) ∧
      (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ V i) ∧
      Disjoint (V 0) (V 1) ∧ ∀ p ∈ V 1, H p < 0 ∧ ‖X p‖ < 1 / 4 := by
  let H := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2
  let X := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).1
  let V : Fin 2 → Set UnitTwoSphere := ![{p | -beta < H p}, {p | H p < -31 / 32}]
  let K : Fin 2 → Set UnitTwoSphere :=
    ![{p | 0 ≤ H p}, {p | H p ≤ 0 ∧ ‖X p‖ ≤ 1 / 8}]
  have hH : Continuous H := (heightCoordinates.continuous.comp continuous_subtype_val).snd
  have hX : Continuous X := (heightCoordinates.continuous.comp continuous_subtype_val).fst
  have hunit (p : UnitTwoSphere) : ‖X p‖ ^ 2 + H p ^ 2 = 1 :=
    sphere_height_coordinates_sq p
  have hneg (p : UnitTwoSphere) : H (-p) = -H p := by
    change (heightCoordinates (-(p : E3))).2 = -(heightCoordinates (p : E3)).2
    exact congrArg Prod.snd (heightCoordinates.map_neg (p : E3))
  have hcap_image (a : ℝ) (ha : -1 < a) :
      northSpherePoint '' ball (0 : E2) (Real.sqrt ((1 - a) / (1 + a))) =
        {p : UnitTwoSphere | a < H p} := by
    have hden : 0 < 1 + a := by linarith
    have hwiff (w : E2) :
        w ∈ ball (0 : E2) (Real.sqrt ((1 - a) / (1 + a))) ↔
          a < H (northSpherePoint w) := by
      rw [mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg w)]
      change ‖w‖ ^ 2 < (1 - a) / (1 + a) ↔
        a < (heightCoordinates (northSpherePoint w : E3)).2
      rw [northSpherePoint_coordinates]
      have hD : 0 < 1 + ‖w‖ ^ 2 := by positivity
      rw [lt_div_iff₀ hden, lt_div_iff₀ hD]
      constructor <;> intro h <;> nlinarith
    ext p
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hwiff w).mp hw
    · intro hp
      have hpN : p ∈ northSphereDomain := ha.trans hp
      refine ⟨northSphereCoordinate p, ?_, northSpherePoint_coordinate hpN⟩
      apply (hwiff _).mpr
      rwa [northSpherePoint_coordinate hpN]
  have hcap_connected (a : ℝ) (ha : -1 < a) :
      IsPreconnected {p : UnitTwoSphere | a < H p} := by
    rw [← hcap_image a ha]
    exact (convex_ball (0 : E2) (Real.sqrt ((1 - a) / (1 + a)))).isPreconnected.image
      northSpherePoint northSpherePoint_contMDiff.continuous.continuousOn
  have hnegset : Neg.neg '' {p : UnitTwoSphere | (31 : ℝ) / 32 < H p} = V 1 := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change (31 : ℝ) / 32 < H q at hq
      change H (-q) < -31 / 32
      rw [hneg]
      linarith
    · intro hp
      change H p < -31 / 32 at hp
      refine ⟨-p, ?_, neg_neg p⟩
      change (31 : ℝ) / 32 < H (-p)
      rw [hneg]
      linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact isOpen_lt continuous_const hH
    · exact isOpen_lt hH continuous_const
  · intro i
    fin_cases i
    · exact hcap_connected (-beta) (by linarith)
    · change IsPreconnected (V 1)
      rw [← hnegset]
      exact (hcap_connected ((31 : ℝ) / 32) (by norm_num)).image
        Neg.neg continuous_neg.continuousOn
  · intro i
    fin_cases i
    · exact (isClosed_le continuous_const hH).isCompact
    · exact ((isClosed_le hH continuous_const).inter
        (isClosed_le hX.norm continuous_const)).isCompact
  · intro i p hp
    fin_cases i
    · change 0 ≤ H p at hp
      change -beta < H p
      linarith
    · change H p ≤ 0 ∧ ‖X p‖ ≤ 1 / 8 at hp
      change H p < -31 / 32
      have hx2 : ‖X p‖ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hp.2
      by_contra hbad
      have hh : -31 / 32 ≤ H p := le_of_not_gt hbad
      have hprod : 0 ≤ (-H p) * (H p + 31 / 32) :=
        mul_nonneg (neg_nonneg.mpr hp.1) (by linarith)
      nlinarith [hunit p]
  · apply Set.disjoint_left.mpr
    intro p hp hpc
    change -beta < H p at hp
    change H p < -31 / 32 at hpc
    linarith
  · intro p hp
    change H p < -31 / 32 at hp
    refine ⟨by linarith, ?_⟩
    by_contra hbad
    have hx : (1 : ℝ) / 4 ≤ ‖X p‖ := le_of_not_gt hbad
    nlinarith [hunit p, sq_nonneg (H p + 31 / 32), sq_nonneg (‖X p‖ - 1 / 4)]

end PoincareConjecture.M25.Topology3D
