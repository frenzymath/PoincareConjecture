import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.JordanFillingCoverage
import Mathlib.Topology.MetricSpace.Bounded








set_option autoImplicit false
open Set Bornology
namespace PoincareConjecture.M76

theorem bounded_open_subset_of_frontier_subset_closed_side
    {X : Type*} [PseudoMetricSpace X] {U V : Set X}
    (hV : IsOpen V) (hVb : IsBounded V)
    (hreg : interior (closure U) = U)
    (hout : IsPreconnected (closure U)ᶜ) (houtu : ¬ IsBounded (closure U)ᶜ)
    (hfront : frontier V ⊆ closure U) : V ⊆ U := by
  have hcover : (closure U)ᶜ ⊆ V ∪ (closure V)ᶜ := by
    intro x hx
    by_cases hv : x ∈ V
    · exact Or.inl hv
    · refine Or.inr (fun hcl => hx (hfront ?_))
      rw [hV.frontier_eq]
      exact ⟨hcl,hv⟩
  have hdis : Disjoint V (closure V)ᶜ :=
    disjoint_left.mpr (fun _ hx hn => hn (subset_closure hx))
  have houtV : (closure U)ᶜ ⊆ (closure V)ᶜ := by
    rcases hout.subset_or_subset hV isClosed_closure.isOpen_compl hdis hcover with hh | hh
    · exact False.elim (houtu (hVb.subset hh))
    · exact hh
  have hsub : V ⊆ closure U := by
    intro x hx
    by_contra hn
    exact houtV hn (subset_closure hx)
  exact hreg ▸ interior_maximal hsub hV

theorem exists_bounded_side_avoiding_common_rim_disk
    {X : Type*} [PseudoMetricSpace X] {U V T W C0 C1 : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hUb : IsBounded U) (hVb : IsBounded V)
    (hUreg : interior (closure U) = U) (hVreg : interior (closure V) = V)
    (hUout : IsPreconnected (closure U)ᶜ) (hVout : IsPreconnected (closure V)ᶜ)
    (hUunbounded : ¬ IsBounded (closure U)ᶜ)
    (hVunbounded : ¬ IsBounded (closure V)ᶜ)
    (hTc : IsPreconnected T)
    (hTU : Disjoint T (frontier U)) (hTV : Disjoint T (frontier V))
    (hUf : frontier U = W ∪ C0) (hVf : frontier V = W ∪ C1)
    (hC0 : C0 ⊆ closure T) (hC1 : C1 ⊆ closure T)
    (hdiff : frontier U ≠ frontier V) :
    Disjoint (closure U) T ∨ Disjoint (closure V) T := by
  have hside {O : Set X} (hO : IsOpen O) (hTO : Disjoint T (frontier O)) :
      T ⊆ O ∨ Disjoint (closure O) T := by
    have hcover : T ⊆ O ∪ (closure O)ᶜ := by
      intro x hx
      by_cases ho : x ∈ O
      · exact Or.inl ho
      · refine Or.inr (fun hcl => disjoint_left.mp hTO hx ?_)
        rw [hO.frontier_eq]
        exact ⟨hcl,ho⟩
    have hdis : Disjoint O (closure O)ᶜ :=
      disjoint_left.mpr (fun _ hx hn => hn (subset_closure hx))
    rcases hTc.subset_or_subset hO isClosed_closure.isOpen_compl hdis hcover with hh | hh
    · exact Or.inl hh
    · exact Or.inr (disjoint_left.mpr (fun x hx ht => hh ht hx))
  rcases hside hU hTU with hTinU | hh
  · rcases hside hV hTV with hTinV | hh
    · have hUV : U ⊆ V := bounded_open_subset_of_frontier_subset_closed_side hU hUb
        hVreg hVout hVunbounded (by
          rw [hUf]
          exact union_subset (fun x hx => frontier_subset_closure (hVf.symm ▸ Or.inl hx))
            (hC0.trans (closure_mono hTinV)))
      have hVU : V ⊆ U := bounded_open_subset_of_frontier_subset_closed_side hV hVb
        hUreg hUout hUunbounded (by
          rw [hVf]
          exact union_subset (fun x hx => frontier_subset_closure (hUf.symm ▸ Or.inl hx))
            (hC1.trans (closure_mono hTinU)))
      exact False.elim (hdiff (congrArg frontier (Subset.antisymm hUV hVU)))
    · exact Or.inr hh
  · exact Or.inl hh

end PoincareConjecture.M76
