import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedPatchData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedCoveredJoinPatch

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_nested_patch_data
    (gamma : Bool → ℝ → AnnulusCoordinates) (T b : Bool → ℝ)
    (hg : ∀ e, ContDiff ℝ ∞ (gamma e)) (hb : ∀ e, b e ∈ Ioo (0 : ℝ) (T e))
    {speed : ℝ} (hspeed : 0 < speed) (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e)))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (hregular : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (hpK : gamma false (T false) ∉ K)
    (havoid : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), gamma e t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ K) (hfV : frontier V = frontier U)
    (P : M64IntrinsicJoinedBandPatch gamma T b U) :
    ∃ delta > 0, ∀ sa ∈ Ioo (0 : ℝ) delta, ∀ z ∈ Ioo (0 : ℝ) delta,
      ∀ sb ∈ Ioo (0 : ℝ) delta,
        ∃ Q : M64IntrinsicJoinedBandPatch gamma T b U,
          Q.direction = P.direction ∧ Q.left_length = sa ∧
          Q.middle_length = z ∧ Q.right_length = sb ∧
          (∀ e, ∀ q, (Q.band e).coordinates q = (P.band e).coordinates q) ∧
          (∀ e, (Q.band e).carrier ⊆ (P.band e).carrier) ∧
          (∀ e : Bool,
            (Q.band e).carrier ∩ (if e then (P.band e).rightCut else (P.band e).leftCut) =
              (if e then (Q.band e).rightCut else (Q.band e).leftCut)) ∧
          ∀ e : Bool, ∀ p ∈ (if e then Ico 0 (b e) else Ioc (b e) (T e)),
            ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma e p ∈ W ∧
              W ∩ closure U ⊆ (Q.band false).carrier ∪ (Q.band true).carrier := by
  obtain ⟨delta, hdelta, hpatch⟩ := m64Intrinsic_exists_nested_covered_join_patch
    (hg false) (hg true) (hb false).1 (hb false).2 (hb true).1 (hb true).2 hspeed
    (hinj false) (hinj true) hjoin hreg htan hab (hregular false) (hregular true)
    hK hpK (havoid false) (havoid true) hU hV hUV hfront hfV (P.frame false) (P.frame true)
    (P.increasing false) (P.increasing true) (P.band false) (P.band true)
    (P.left_base false) (P.right_base false) (P.left_base true) (P.right_base true)
    (by simp only [Prod.eta, ContinuousLinearEquiv.apply_symm_apply])
    (by simp only [Prod.eta, ContinuousLinearEquiv.apply_symm_apply])
    (P.lower_arc false) (P.lower_arc true) (P.occupied false) (P.occupied true)
    (P.off_lower false) (P.off_lower true) P.intersection
  refine ⟨delta, hdelta, ?_⟩
  intro sa hsa z hz sb hsb
  obtain ⟨Q0, Q1, hcoords0, hcoords1, hlower0, hlower1, _, _, hsub0, hsub1,
      hU0, hU1, hopen0, hopen1, hcut0, hcut1, _, _, hinter, hcover0, hcover1⟩ :=
    hpatch sa hsa z hz sb hsb
  let Q : M64IntrinsicJoinedBandPatch gamma T b U :=
    { frame := P.frame
      graph := P.graph
      left := P.left
      right := P.right
      increasing := P.increasing
      direction := P.direction
      left_length := sa
      middle_length := z
      right_length := sb
      band := fun e => Bool.rec Q0 Q1 e
      left_base := P.left_base
      right_base := P.right_base
      transverse := P.transverse
      tangent := P.tangent
      lower_arc := by
        intro e
        cases e
        · exact hlower0
        · exact hlower1
      occupied := by
        intro e
        cases e
        · exact hU0
        · exact hU1
      off_lower := by
        intro e
        cases e
        · exact hopen0
        · exact hopen1
      intersection := hinter }
  refine ⟨Q, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro e q
    cases e
    · exact hcoords0 q
    · exact hcoords1 q
  · intro e
    cases e
    · exact hsub0
    · exact hsub1
  · intro e
    cases e
    · exact hcut0
    · exact hcut1
  · intro e p hp
    cases e
    · exact hcover0 p hp
    · exact hcover1 p hp

end PoincareConjecture
