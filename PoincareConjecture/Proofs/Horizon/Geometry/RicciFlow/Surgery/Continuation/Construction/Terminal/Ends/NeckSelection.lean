import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckPacking
import Mathlib.Order.Zorn









noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_finite_disjoint_neck_selection (Q : SingularLimitConclusion H)
    {epsilon q : ℝ} (hε : epsilon < 1 / 2) (hq : 0 < q)
    (candidates : Set (TerminalStrongNeck Q.extension epsilon))
    (hlevel : ∀ N ∈ candidates, Q.terminal_scalar N.center = q) :
    ∃ selected : Finset (TerminalStrongNeck Q.extension epsilon),
      (∀ N ∈ selected, N ∈ candidates) ∧
      (selected : Set (TerminalStrongNeck Q.extension epsilon)).Pairwise
        (fun N P => Disjoint N.carrier P.carrier) ∧
      ∀ N ∈ candidates, ∃ P ∈ selected, (N.carrier ∩ P.carrier).Nonempty := by
  classical
  let admissible : Set (Set (TerminalStrongNeck Q.extension epsilon)) :=
    {S | S ⊆ candidates ∧ S.Pairwise fun N P => Disjoint N.carrier P.carrier}
  obtain ⟨S, hmax⟩ := zorn_subset admissible (by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · rintro N ⟨s, hs, hN⟩
      exact (hc hs).1 hN
    · rintro N ⟨s, hs, hN⟩ P ⟨t, ht, hP⟩ hNP
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 (hst hN) hP hNP
      · exact (hc hs).2 hN (hts hP) hNP)
  have hS : S ⊆ candidates ∧ S.Pairwise fun N P => Disjoint N.carrier P.carrier := hmax.prop
  have : Finite S := Q.finite_disjoint_necks_at_scalar_level hε hq
    (fun N : S => N.val) (fun N => hlevel N (hS.1 N.property))
    (fun N P hNP => hS.2 N.property P.property (fun h => hNP (Subtype.ext h)))
  let hfinite : S.Finite := Set.toFinite S
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · intro N hN
    exact hS.1 (hfinite.mem_toFinset.mp hN)
  · simpa only [Set.Finite.coe_toFinset] using hS.2
  · intro N hN
    by_contra hnone
    have hdis (P) (hP : P ∈ S) : Disjoint N.carrier P.carrier := by
      apply disjoint_iff_inter_eq_empty.mpr
      exact Set.not_nonempty_iff_eq_empty.mp (fun h =>
        hnone ⟨P, hfinite.mem_toFinset.mpr hP, h⟩)
    have hadm : insert N S ∈ admissible := by
      refine ⟨insert_subset hN hS.1, ?_⟩
      rw [pairwise_insert]
      exact ⟨hS.2, fun P hP _ => ⟨hdis P hP, (hdis P hP).symm⟩⟩
    have hNS : N ∈ S := hmax.mem_of_prop_insert hadm
    have hself := N.central_sphere_subset N.center_on_central_sphere
    exact disjoint_left.mp (hdis N hNS) hself hself

end PoincareConjecture.SingularLimitConclusion
