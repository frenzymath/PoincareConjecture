import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChainNestedPatch
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcMatchedBandCoverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_chain_patch_covers_attachment
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (ha : 0 < a) (hb : b < T) (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (E : M64IntrinsicArcBandChain gamma a b U) (terminal : Bool)
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a0 a1 ua wa ub wb ra rb : ℝ}
    (P : ObliqueBandFaces F f a0 a1 ua wa ub wb ra rb)
    (hbase : (P.endpointEdge terminal).map 0 = gamma (if terminal then a else b))
    (hcut : (if terminal then P.rightCut else P.leftCut) =
      segment ℝ (gamma (if terminal then a else b))
        (gamma (if terminal then a else b) + E.length • E.direction (if terminal then a else b)))
    (hcontact : ∀ i, P.carrier ∩ (E.band i).carrier =
      (if terminal then (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
        else (if E.cut i.succ = b then (E.band i).rightCut else ∅)))
    (hlower : P.lowerArc ⊆ gamma '' Icc 0 T) (hsub : P.carrier ⊆ closure U) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma (if terminal then a else b) ∈ W ∧
      W ∩ closure U ⊆ (⋃ i, (E.band i).carrier) ∪ P.carrier := by
  have hn := E.count_pos
  have hab : a < b := by
    have hlt : (0 : Fin (E.count + 1)) < Fin.last E.count := hn
    simpa only [E.first_cut, E.last_cut] using E.cut_strictMono hlt
  have hpoint : (if terminal then a else b) ∈ Ioo (0 : ℝ) T := by
    cases terminal
    · exact ⟨ha.trans hab, hb⟩
    · exact ⟨ha, hab.trans hb⟩
  let i : Fin E.count := ⟨if terminal then 0 else E.count - 1, by
    cases terminal
    · change E.count - 1 < E.count
      omega
    · exact hn⟩
  have hi : E.cut (if terminal then i.castSucc else i.succ) =
      (if terminal then a else b) := by
    cases terminal
    · have hlast : i.succ = Fin.last E.count := by
        apply Fin.ext
        change (E.count - 1) + 1 = E.count
        omega
      change E.cut i.succ = b
      rw [hlast]
      exact E.last_cut
    · have hfirst : i.castSucc = 0 := by apply Fin.ext; rfl
      change E.cut i.castSucc = a
      rw [hfirst]
      exact E.first_cut
  have hbaseE : ((E.band i).endpointEdge (!terminal)).map 0 =
      gamma (if terminal then a else b) := by
    rw [E.endpoint_zero]
    apply congrArg gamma
    cases terminal <;> exact hi
  have hcutE : (if !terminal then (E.band i).rightCut else (E.band i).leftCut) =
      segment ℝ (gamma (if terminal then a else b))
        (gamma (if terminal then a else b) +
          E.length • E.direction (if terminal then a else b)) := by
    cases terminal
    · change (E.band i).rightCut = segment ℝ (gamma b) (gamma b + E.length • E.direction b)
      change E.cut i.succ = b at hi
      rw [E.right_cut, hi]
    · change (E.band i).leftCut = segment ℝ (gamma a) (gamma a + E.length • E.direction a)
      change E.cut i.castSucc = a at hi
      rw [E.left_cut, hi]
  have hcuts : ((E.band i).endpointEdge (!terminal)).map '' Icc (0 : ℝ) 1 =
      (P.endpointEdge terminal).map '' Icc (0 : ℝ) 1 := by
    rw [(E.band i).endpointEdge_image, P.endpointEdge_image, hcutE, hcut]
  have hinter : (E.band i).carrier ∩ P.carrier ⊆ frontier (E.band i).carrier := by
    have heq : (E.band i).carrier ∩ P.carrier =
        (if !terminal then (E.band i).rightCut else (E.band i).leftCut) := by
      rw [inter_comm, hcontact]
      cases terminal
      · change (if E.cut i.succ = b then (E.band i).rightCut else ∅) = (E.band i).rightCut
        exact if_pos hi
      · change (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) = (E.band i).leftCut
        exact if_pos hi
    rw [heq, ← (E.band i).endpointEdge_image (!terminal)]
    exact (E.band i).endpointEdge_subset_frontier (!terminal)
  obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_matched_bands_cover_region hg hinj
    hregular hpoint hK (havoid _ hpoint) hU hV hUV hfront hfV (E.band i) P
    (!terminal) terminal hbaseE hbase hcuts hinter
    ((E.lower_subset i).trans (image_mono (Icc_subset_Icc ha.le hb.le)))
    hlower (E.occupied i) hsub
  refine ⟨W, hW, hpW, hcover.trans ?_⟩
  exact union_subset_union (fun p hp => mem_iUnion.mpr ⟨i, hp⟩) Subset.rfl

end PoincareConjecture
