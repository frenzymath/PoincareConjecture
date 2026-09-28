import PoincareConjecture.Proofs.M54.ConnectedSum.Reconstruction
import PoincareConjecture.Proofs.M55.Mathlib.SimplyConnected

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

set_option linter.style.haveILetI false in

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

end PoincareConjecture
