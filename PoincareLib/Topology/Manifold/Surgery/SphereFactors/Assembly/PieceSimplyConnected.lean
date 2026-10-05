import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Reconstruction
import PoincareLib.Topology.Homotopy.Groups.SimplyConnected

/-!
# Simple connectedness of every finite-assembly piece

M54 supplies a based fundamental-group factor certificate from each original
summand into the assembled carrier.  A simply connected assembled carrier has
subsingleton fundamental groups, so the factor groups are subsingleton too.
The connected, locally path-connected manifold carrier then satisfies the
Mathlib bridge back to `SimplyConnectedSpace`.

Source: Morgan--Tian Proposition 15.3, pp. 357--358 (the summand injections),
with the topological bridge from Mathlib's simply-connected fundamental
groupoid criterion.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

set_option linter.style.haveILetI false in
/-- Every connected M72 assembly piece is simply connected: M54's factor
certificate makes its fundamental group a subsingleton, and the manifold
bridge turns that certificate into `SimplyConnectedSpace`. Source:
Morgan--Tian Proposition 15.3, pp. 357--358, plus the Mathlib fundamental
groupoid criterion. -/
theorem SmoothFiniteConnectedSumAssembly.piece_simplyConnected
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (R : SmoothFiniteConnectedSumAssembly pieces C)
    [SimplyConnectedSpace C.carrier]
    (i : Fin n)
    (hconn : IsConnected (Set.univ : Set (pieces i).carrier)) :
    SimplyConnectedSpace (pieces i).carrier := by
  letI : ConnectedSpace (pieces i).carrier := connectedSpace_iff_univ.mpr hconn
  letI : LocallyPathConnectedSpace (pieces i).carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3))
      (pieces i).carrier
  letI : PathConnectedSpace (pieces i).carrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  have hgroups : ∀ x : (pieces i).carrier,
      Subsingleton (FundamentalGroup (pieces i).carrier x) := by
    intro x
    obtain ⟨y, ⟨D⟩⟩ := R.piece_factor i x
    exact D.target_subsingleton
  exact simplyConnected_of_pathConnected_of_fundamentalGroup_subsingleton
    (pieces i).carrier hgroups

end PoincareMT
