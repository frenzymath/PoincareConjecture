import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.RemoveBall
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Collars
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.FactorData

/-! Adapted from Mapher `PoincareMT/Proofs/M54/ConnectedSum/Factors.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# The group factors of one connected sum

Apply the retraction form of van Kampen to each collar cover, then fill
the removed ball and transport the basepoint. This supplies both factor
maps and injective sections in Morgan--Tian Proposition 15.3, pp. 357-358.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT

namespace SurgeryBallEmbedding

/-- A punctured-side open cover supplies the group factor of the original
summand, at every original basepoint (MT Proposition 15.3, pp. 357-358). -/
theorem factor_of_open_cover {A C : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
    (U V : Set C.carrier) (e : SurgeryRegionEquivalence A C B.closedBallᶜ U)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hW : IsSimplyConnected (U ∩ V)) (x : A.carrier) :
    ∃ y : C.carrier,
      Nonempty (RepairedGroupFactorData (FundamentalGroup C.carrier y)
        (FundamentalGroup A.carrier x)) := by
  obtain ⟨a, ⟨ea⟩⟩ := B.exists_complement_group_equiv x
  let b := e.toHomeomorph a
  obtain ⟨r, hr⟩ := VanKampen.exists_retraction U V b hU hV hcover hW
  refine ⟨b.1, ⟨?_⟩⟩
  exact (RepairedGroupFactorData.ofRetraction r
    (FundamentalGroup.map (VanKampen.inclusion U) b) hr).trans
      (RepairedGroupFactorData.ofMulEquiv
        ((e.toHomeomorph.fundamentalGroupMulEquiv a).symm.trans ea))

end SurgeryBallEmbedding

namespace SmoothConnectedSumData

variable {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)

include S

/-- The first summand group is a retract of a group of the connected sum,
with explicit basepoint choice (MT Proposition 15.3, pp. 357-358). -/
theorem first_factor (x : A.carrier) :
    ∃ y : C.carrier,
      Nonempty (RepairedGroupFactorData (FundamentalGroup C.carrier y)
        (FundamentalGroup A.carrier x)) := by
  apply S.first_ball.factor_of_open_cover S.first_region
    (S.second_region ∪ S.collarBand (-1) 1) S.first_identify
    S.first_open (S.second_open.union S.collar_open) S.first_cover
  rw [S.first_overlap]
  exact S.collarBand_simplyConnected (-1) 0 (by norm_num) le_rfl (by norm_num)

/-- The second summand has the same factor certificate, using the positive
collar in MT Proposition 15.3 (pp. 357-358). -/
theorem second_factor (x : B.carrier) :
    ∃ y : C.carrier,
      Nonempty (RepairedGroupFactorData (FundamentalGroup C.carrier y)
        (FundamentalGroup B.carrier x)) := by
  apply S.second_ball.factor_of_open_cover S.second_region
    (S.first_region ∪ S.collarBand (-1) 1) S.second_identify
    S.second_open (S.first_open.union S.collar_open) S.second_cover
  rw [S.second_overlap]
  exact S.collarBand_simplyConnected 0 1 (by norm_num) (by norm_num) le_rfl

end SmoothConnectedSumData

end PoincareMT
