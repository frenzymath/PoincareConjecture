import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Limits.SelectedInteriorWall
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Selected necks chosen before every finite ray family

The actual scalar barrier selects a whole neck above each prescribed
height. The fixed cofinal height sequence is independent of all later
finite ray families and chord-separation parameters.
Source: Morgan--Tian Lemma 10.27, p. 261; M28 derivation 155.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

/-- The retained scalar geometry selects an entire cofinal neck
sequence before any rays are tested. No ordering of the original chain
indices is presumed. Source: Lemma 10.27, p. 261; derivation 155. -/
theorem exists_cofinal_selected_neck_sequence
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < R x) :
    ∃ (c : ℕ → ℝ) (i : ℕ → ℤ),
      (∀ n, 1 / 2 < c n ∧ c n < 1) ∧ Tendsto c atTop (𝓝 1) ∧
      (∀ n, i n ∈ T.chain.shape.active) ∧
      ∀ n, (T.chain.neck (i n)).carrier ⊆ A.tail true (c n) := by
  classical
  let c : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 4)
  have hc (n : ℕ) : 1 / 2 < c n ∧ c n < 1 := by
    have hden : 0 < (n : ℝ) + 4 := by positivity
    have hinv : 1 / ((n : ℝ) + 4) ≤ (1 / 4 : ℝ) := by
      apply (div_le_div_iff₀ hden (by norm_num)).mpr
      nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    have hpos : 0 < 1 / ((n : ℝ) + 4) := one_div_pos.mpr hden
    dsimp only [c]
    constructor <;> linarith only [hinv, hpos]
  have hinvLimit : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 4).2
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hcLimit : Tendsto c atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinvLimit
  choose i hi hwhole using fun n =>
    exists_selected_chain_neck_above_cylinder_level T A R hR hratio hdiverge
      (hc n).1 (hc n).2
  exact ⟨c, i, hc, hcLimit, hi, hwhole⟩

end PoincareMT.M28
