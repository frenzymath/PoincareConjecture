import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryModulus

/-!
# Algebra of free periodic degree-one lifts

Monotone Lipschitz degree-one lifts are closed under identity and composition.
These elementary operations are useful when several boundary collars are
composed; no inverse or strict monotonicity is inferred.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT

/-- The identity monotone Lipschitz degree-one lift. Proof expansion for Morgan-Tian (2007),
Lemma 19.15, pp. 447-449. -/
noncomputable def M64PeriodicDegreeOneLift.identity : M64PeriodicDegreeOneLift where
  map := id
  monotone := monotone_id
  period_shift := by intro x; simp [curvePeriod]
  lipschitz_constant := 1
  lipschitz_nonnegative := by norm_num
  lipschitz_on := by intro x y; simp

/-- Composition of actual monotone Lipschitz degree-one lifts with the product Lipschitz
constant. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
noncomputable def M64PeriodicDegreeOneLift.comp
    (outer inner : M64PeriodicDegreeOneLift) : M64PeriodicDegreeOneLift where
  map := outer.map ∘ inner.map
  monotone := outer.monotone.comp inner.monotone
  period_shift := by
    intro x
    change outer.map (inner.map (x + curvePeriod)) =
      outer.map (inner.map x) + curvePeriod
    rw [inner.period_shift, outer.period_shift]
  lipschitz_constant := outer.lipschitz_constant * inner.lipschitz_constant
  lipschitz_nonnegative := mul_nonneg outer.lipschitz_nonnegative
    inner.lipschitz_nonnegative
  lipschitz_on := by
    intro x y
    calc
      |(outer.map ∘ inner.map) x - (outer.map ∘ inner.map) y| ≤
          outer.lipschitz_constant * |inner.map x - inner.map y| := by
        simpa only [Function.comp_apply] using outer.lipschitz_on (inner.map x) (inner.map y)
      _ ≤ outer.lipschitz_constant *
          (inner.lipschitz_constant * |x - y|) := by
        exact mul_le_mul_of_nonneg_left (inner.lipschitz_on x y)
          outer.lipschitz_nonnegative
      _ = (outer.lipschitz_constant * inner.lipschitz_constant) * |x - y| := by ring

/-- The map of the composite degree-one lift is literal function composition. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64PeriodicDegreeOneLift.comp_map
    (outer inner : M64PeriodicDegreeOneLift) (x : ℝ) :
    (outer.comp inner).map x = outer.map (inner.map x) := rfl

/-- Composition of degree-one lifts is associative, including their recorded Lipschitz
constants. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64PeriodicDegreeOneLift.comp_assoc
    (a b c : M64PeriodicDegreeOneLift) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  cases a
  cases b
  cases c
  simp [M64PeriodicDegreeOneLift.comp, Function.comp_def]
  ring

/-- The identity lift is a left identity for lift composition. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64PeriodicDegreeOneLift.identity_comp
    (a : M64PeriodicDegreeOneLift) :
    M64PeriodicDegreeOneLift.identity.comp a = a := by
  cases a
  simp [M64PeriodicDegreeOneLift.identity, M64PeriodicDegreeOneLift.comp]

/-- The identity lift is a right identity for lift composition. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64PeriodicDegreeOneLift.comp_identity
    (a : M64PeriodicDegreeOneLift) :
    a.comp M64PeriodicDegreeOneLift.identity = a := by
  cases a
  simp [M64PeriodicDegreeOneLift.identity, M64PeriodicDegreeOneLift.comp]

end PoincareMT
