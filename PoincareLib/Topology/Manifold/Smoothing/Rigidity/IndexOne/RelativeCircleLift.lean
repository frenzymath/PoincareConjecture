import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.StandardHierarchyCoordinates
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting

/-!
# Relative phase lifts for the interval-torus hierarchy

Lift the displacement along the supplied relative homotopy, starting at
zero. Uniqueness along each time interval fixes the real lift on every
marked point, even when the mark has two components. This retains the
whole old boundary in Hamilton 1976, Lemma 3, pp. 65--67, and Waldhausen
1968, Theorem 6.1, p. 77.
-/

set_option autoImplicit false

open Set unitInterval

namespace AddCircle

/-- The given relative homotopy constructs a real displacement lift
vanishing on the entire mark, without any connectedness hypothesis. -/
theorem exists_homotopyRel_difference_lift
    {X : Type*} [TopologicalSpace X] (p : ℝ) [Fact (0 < p)]
    {f g : C(X, AddCircle p)} {A : Set X} (F : f.HomotopyRel g A) :
    ∃ l : C(X, ℝ), (∀ x, (l x : AddCircle p) = g x - f x) ∧
      ∀ x ∈ A, l x = 0 := by
  let H : C(I × X, AddCircle p) :=
    ⟨fun z => F z - f z.2, F.continuous.sub (f.continuous.comp continuous_snd)⟩
  let zero : C(X, ℝ) := ContinuousMap.const X 0
  have hH0 (x : X) : H (0, x) = (zero x : AddCircle p) := by
    change F (0, x) - f x = 0
    rw [F.apply_zero, sub_self]
  let cov := isCoveringMap_coe p
  let T := cov.liftHomotopy H zero hH0
  have hT (t : I) (x : X) : (T (t, x) : AddCircle p) = H (t, x) :=
    congrFun (cov.liftHomotopy_lifts H zero hH0) (t, x)
  have hT0 (x : X) : T (0, x) = 0 := cov.liftHomotopy_zero H zero hH0 x
  let l : C(X, ℝ) := T.comp ((ContinuousMap.const X (1 : I)).prodMk
    (ContinuousMap.id X))
  refine ⟨l, ?_, ?_⟩
  · intro x
    change (T (1, x) : AddCircle p) = g x - f x
    rw [hT]
    change F (1, x) - f x = g x - f x
    rw [F.apply_one]
  · intro x hx
    have hcont : Continuous (fun t : I => T (t, x)) :=
      T.continuous.comp (continuous_id.prodMk continuous_const)
    have hconst := cov.const_of_comp hcont (fun t s => by
      rw [hT, hT]
      change F (t, x) - f x = F (s, x) - f x
      rw [F.eq_fst t hx, F.eq_fst s hx]) (1 : I) 0
    exact hconst.trans (hT0 x)

end AddCircle

namespace PoincareMT.M76

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

private instance : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩

/-- The original index-one homotopy lifts the last phase displacement
with real value zero on both complete original boundary tori. -/
theorem exists_hamiltonOne_relative_phase_lift
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ l : C(H, ℝ),
      (∀ x, (l x : C) = (hamiltonOneHierarchyCoordinates (phi x)).2 -
        (hamiltonOneHierarchyCoordinates x).2) ∧
      ∀ x ∈ B, l x = 0 := by
  let q : C(H, C) := ⟨fun x => (hamiltonOneHierarchyCoordinates x).2,
    continuous_snd.comp hamiltonOneHierarchyCoordinates.continuous⟩
  let G : q.HomotopyRel (q.comp phi) B :=
    { toFun := fun z => q (F z)
      continuous_toFun := q.continuous.comp F.continuous
      map_zero_left := by intro x; rw [F.apply_zero]; rfl
      map_one_left := by intro x; change q (F (1, x)) = q (phi x); rw [F.apply_one]
      prop' := by intro t x hx; change q (F (t, x)) = q x; rw [F.eq_fst t hx]; rfl }
  exact AddCircle.exists_homotopyRel_difference_lift (4 * (128 : ℝ)) G

end PoincareMT.M76
