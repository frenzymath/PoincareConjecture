import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.MarkedAnnulusConstruction
import PoincareLib.Topology.Covering.Universal.PathHomotopy
import Mathlib.GroupTheory.OrderOfElement

/-!
# Essentiality of positive boundary-loop rims

Fundamental-group injection preserves every positive iterate of an
infinite-order boundary loop. Its entire rim remains non-nullhomotopic
under the actual boundary approximation homotopy.
See Waldhausen, Lemma 5.1, p. 72.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

open Dehn

local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

/-- The whole rim map carrying a positive iterate of an infinite-order
boundary loop cannot contract in the ambient region. -/
theorem not_nullhomotopic_of_injective_boundary_power
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (i : C(E, X)) (x : E) (hi : Function.Injective (FundamentalGroup.map i x))
    (alpha : Path x x)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0)
    (n : ℕ) (hn : 0 < n) (gamma : C(Q2, X))
    (hgamma : ∀ s : unitInterval, gamma (squareRimLoop s) =
      i (boundaryLoopIterate alpha n s)) :
    ¬ gamma.Nullhomotopic := by
  intro hnull
  have h := Path.Homotopic.map_nullhomotopic_of_nullhomotopic hnull squareRimLoop
  have hbase : gamma squareRimBase = i x := by
    simpa using hgamma 0
  have hleft : (squareRimLoop.map gamma.continuous).toContinuousMap =
      ((boundaryLoopIterate alpha n).map i.continuous).toContinuousMap :=
    ContinuousMap.ext hgamma
  have hright : (Path.refl (gamma squareRimBase)).toContinuousMap =
      (Path.refl (i x)).toContinuousMap := ContinuousMap.ext (fun _ => hbase)
  change (squareRimLoop.map gamma.continuous).toContinuousMap.HomotopicRel
    (Path.refl (gamma squareRimBase)).toContinuousMap {0, 1} at h
  rw [hleft, hright] at h
  have heq : (FundamentalGroup.map i x)
      ((FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) ^ n) = 1 := by
    rw [boundaryLoopIterate_class]
    exact Path.Homotopic.Quotient.eq.mpr h
  exact (orderOf_eq_zero_iff'.mp ha n hn) (hi (heq.trans (map_one _).symm))

/-- Actual homotopy of the complete rim transports the disk obstruction
to the approximated rim, without a radial retraction of the region. -/
theorem not_nullhomotopic_of_boundary_power_homotopy
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (i : C(E, X)) (x : E) (hi : Function.Injective (FundamentalGroup.map i x))
    (alpha : Path x x)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0)
    (n : ℕ) (hn : 0 < n) (gamma gamma₀ : C(Q2, X))
    (hgamma : ∀ s : unitInterval, gamma (squareRimLoop s) =
      i (boundaryLoopIterate alpha n s))
    (H : gamma.Homotopic gamma₀) :
    ¬ gamma₀.Nullhomotopic := by
  rintro ⟨y, hy⟩
  exact not_nullhomotopic_of_injective_boundary_power i x hi alpha ha n hn gamma hgamma
    ⟨y, H.trans hy⟩

end PoincareMT.M76
