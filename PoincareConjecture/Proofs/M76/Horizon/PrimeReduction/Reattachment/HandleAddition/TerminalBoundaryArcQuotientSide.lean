import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcLift

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem disjoint_image_of_injective_closed_side
    {X Y : Type*} [NormedAddCommGroup X] [AddCommGroup Y]
    (p : X →+ Y) {U T : Set X}
    (hU : IsOpen U) (hT : IsPreconnected T)
    (hi : InjOn p (closure U)) (hdis : Disjoint (closure U) T)
    (hfront : Disjoint (p '' frontier U) (p '' T))
    (hmark : (frontier U ∩ closure T).Nonempty) :
    Disjoint (p '' closure U) (p '' T) := by
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ ⟨t,ht,hpt⟩
  let d := x - t
  have hpd : p d = 0 := by dsimp [d]; rw [map_sub,hpt,sub_self]
  let V := (fun z => d + z) '' T
  have hc : IsPreconnected V := hT.image _ (continuous_const.add continuous_id).continuousOn
  have hvx : x ∈ V := ⟨t,ht,by dsimp [d]; abel⟩
  have hvfront : Disjoint V (frontier U) := by
    apply disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hu
    apply disjoint_left.mp hfront (mem_image_of_mem p hu)
    refine ⟨z,hz,?_⟩
    rw [map_add,hpd,zero_add]
  have hcover : V ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases hu : z ∈ U
    · exact Or.inl hu
    · refine Or.inr (fun hcl => disjoint_left.mp hvfront hz ?_)
      rw [hU.frontier_eq]
      exact ⟨hcl,hu⟩
  have hparts : Disjoint U (closure U)ᶜ :=
    disjoint_left.mpr (fun _ hu hn => hn (subset_closure hu))
  have hVU : V ⊆ U := by
    rcases hc.subset_or_subset hU isClosed_closure.isOpen_compl hparts hcover with hh | hh
    · exact hh
    · exact False.elim (hh hvx hx)
  obtain ⟨m,hmU,hmT⟩ := hmark
  have hdm : d + m ∈ closure U := by
    apply closure_mono hVU
    exact mem_closure_image (continuous_const.add continuous_id).continuousAt hmT
  have heq : d + m = m := hi hdm (frontier_subset_closure hmU) (by
    rw [map_add,hpd,zero_add])
  have hd : d = 0 := add_right_cancel (heq.trans (zero_add m).symm)
  have hxt : x = t := sub_eq_zero.mp hd
  exact disjoint_left.mp hdis hx (hxt ▸ ht)

end PoincareConjecture.M76
