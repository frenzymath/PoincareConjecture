import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedPatchChainContacts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

abbrev m64IntrinsicJoinedBandUnion
    {gamma : Bool → ℝ → AnnulusCoordinates} {T r b : Bool → ℝ}
    {U : Set AnnulusCoordinates}
    (E : ∀ e : Bool, M64IntrinsicArcBandChain (gamma e)
      (if e then b e else r e) (if e then T e - r e else b e) U)
    (P : M64IntrinsicJoinedBandPatch gamma T b U) : Set AnnulusCoordinates :=
  ⋃ e, (⋃ i, ((E e).band i).carrier) ∪ (P.band e).carrier

structure M64IntrinsicJoinedArcCollar
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) (b : Bool → ℝ) where
  attachment : ∀ e, b e ∈ Ioo (0 : ℝ) (T e)
  chain : ∀ e : Bool, M64IntrinsicArcBandChain (gamma e)
    (if e then b e else C.radius e) (if e then T e - C.radius e else b e) U
  patch : M64IntrinsicJoinedBandPatch gamma T b U
  cap_direction : ∀ e : Bool,
    (chain e).direction (if e then T e - C.radius e else C.radius e) =
      C.cap e (true, C.positive e) (0, C.radius e) -
        C.cap e (true, C.positive e) (C.radius e, 0)
  cap_path : ∀ e : Bool, ∀ z ∈ Icc (0 : ℝ) 1,
    gamma e (if e then T e - C.radius e else C.radius e) +
      z • (chain e).direction (if e then T e - C.radius e else C.radius e) ∈ C.carrier e
  opposite_cap : ∀ e i, Disjoint (C.carrier (!e)) ((chain e).band i).carrier
  cap_contact : ∀ (e : Bool) i, C.carrier e ∩ ((chain e).band i).carrier =
    if e then
      (if (chain e).cut i.succ = T e - C.radius e then ((chain e).band i).rightCut else ∅)
    else (if (chain e).cut i.castSucc = C.radius e then ((chain e).band i).leftCut else ∅)
  patch_contact : ∀ (e : Bool) i, (patch.band e).carrier ∩ ((chain e).band i).carrier =
    if e then (if (chain e).cut i.castSucc = b e then ((chain e).band i).leftCut else ∅)
    else (if (chain e).cut i.succ = b e then ((chain e).band i).rightCut else ∅)
  opposite_patch : ∀ e i, Disjoint (patch.band (!e)).carrier ((chain e).band i).carrier
  matched_cut : ∀ e : Bool,
    (if e then (patch.band e).rightCut else (patch.band e).leftCut) =
      segment ℝ (gamma e (b e)) (gamma e (b e) + (chain e).length • (chain e).direction (b e))
  caps_patch_disjoint : ∀ e f, Disjoint (C.carrier e) (patch.band f).carrier
  chains_disjoint : ∀ i j,
    Disjoint ((chain false).band i).carrier ((chain true).band j).carrier
  third_avoids : Disjoint (sigma '' Icc 0 S) (m64IntrinsicJoinedBandUnion chain patch)
  covered : ∀ e, ∀ p ∈ Icc (0 : ℝ) (T e),
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma e p ∈ W ∧
      W ∩ closure U ⊆ (C.carrier false ∪ C.carrier true) ∪
        m64IntrinsicJoinedBandUnion chain patch

namespace M64IntrinsicJoinedArcCollar

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
  (J : M64IntrinsicJoinedArcCollar C b)

theorem bands_closed : IsClosed (m64IntrinsicJoinedBandUnion J.chain J.patch) := by
  apply isClosed_iUnion_of_finite
  intro e
  exact (isClosed_iUnion_of_finite fun i => ((J.chain e).band i).isClosed_carrier).union
    (J.patch.band e).isClosed_carrier

theorem occupied : (C.carrier false ∪ C.carrier true) ∪
    m64IntrinsicJoinedBandUnion J.chain J.patch ⊆ closure U := by
  apply union_subset (union_subset (C.occupied false) (C.occupied true))
  apply iUnion_subset
  intro e
  exact union_subset (iUnion_subset fun i => (J.chain e).occupied i) (J.patch.occupied e)

end M64IntrinsicJoinedArcCollar

end PoincareConjecture
