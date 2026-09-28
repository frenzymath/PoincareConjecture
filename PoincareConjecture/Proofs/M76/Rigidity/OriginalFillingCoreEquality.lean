import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.PlanarRegionSideTransport
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.ChartwisePLBall

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {K Db : Set X} {A : Set E}

theorem eq_core_of_positive_collar (c : E × ℝ → X)
    (hA : IsConnected A) (hc : ContinuousOn c (A ×ˢ I)) (hi : InjOn c (A ×ˢ I))
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ1 : δ ≤ 1)
    (hopen : IsOpen (c '' (A ×ˢ Ioo 0 δ)))
    (b : ChartwisePLBall e Db (c '' (A ×ˢ {ε})))
    (hBC : Db ⊆ K \ (c '' (A ×ˢ Ico 0 ε)))
    (hC : IsConnected (K \ (c '' (A ×ˢ Ico 0 ε)))) :
    Db = K \ (c '' (A ×ˢ Ico 0 ε)) := by
  have hε1 : ε ≤ 1 := hεδ.le.trans hδ1
  have hSO : c '' (A ×ˢ {ε}) ⊆ c '' (A ×ˢ Ioo 0 δ) := by
    apply image_mono
    intro z hz
    have ht : z.2 = ε := mem_singleton_iff.mp hz.2
    refine ⟨hz.1, ?_⟩
    rw [ht]
    exact ⟨hε, hεδ⟩
  have hVfull : A ×ˢ Ioo ε δ ⊆ A ×ˢ I := by
    intro z hz
    exact ⟨hz.1, (hε.trans hz.2.1).le, hz.2.2.le.trans hδ1⟩
  have hVconnected : IsConnected (c '' (A ×ˢ Ioo ε δ)) :=
    (hA.prod (isConnected_Ioo hεδ)).image c (hc.mono hVfull)
  have hVavoid : Disjoint (c '' (A ×ˢ Ioo ε δ)) (frontier Db) := by
    rw [b.frontier_eq]
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have ht : w.2 = ε := mem_singleton_iff.mp hw.2
    have hwI : w ∈ A ×ˢ I := by
      refine ⟨hw.1, ?_⟩
      rw [ht]
      exact ⟨hε.le, hε1⟩
    have hwz : w = z := hi hwI (hVfull hz) heq
    have hzt : z.2 = ε := (congrArg Prod.snd hwz).symm.trans ht
    exact (lt_irrefl ε) (hzt ▸ hz.2.1)
  obtain ⟨z0, hz0⟩ := hA.nonempty
  have hxS : c (z0, ε) ∈ c '' (A ×ˢ {ε}) := ⟨(z0, ε), ⟨hz0, rfl⟩, rfl⟩
  have hxClosure : c (z0, ε) ∈ closure (interior Db) := by
    rw [b.closure_interior]
    exact b.boundary_subset hxS
  obtain ⟨y, hyO, hyInt⟩ := mem_closure_iff.mp hxClosure _ hopen (hSO hxS)
  have hyV : y ∈ c '' (A ×ˢ Ioo ε δ) := by
    obtain ⟨z, hz, rfl⟩ := hyO
    have hge : ε ≤ z.2 := le_of_not_gt (fun h =>
      (hBC (interior_subset hyInt)).2 ⟨z, ⟨hz.1, hz.2.1.le, h⟩, rfl⟩)
    have hne : z.2 ≠ ε := by
      intro ht
      have hS : c z ∈ c '' (A ×ˢ {ε}) := ⟨z, ⟨hz.1, ht⟩, rfl⟩
      have hf : c z ∈ frontier Db := b.frontier_eq.symm ▸ hS
      exact hf.2 hyInt
    exact ⟨z, ⟨hz.1, lt_of_le_of_ne hge (Ne.symm hne), hz.2.2⟩, rfl⟩
  have hVinside : c '' (A ×ˢ Ioo ε δ) ⊆ interior Db := by
    intro x hx
    have hxB : x ∈ Db :=
      (hVconnected.isPreconnected.mem_iff_of_disjoint_frontier hVavoid hx hyV).mpr
        (interior_subset hyInt)
    exact (mem_interior_iff_notMem_frontier hxB).mpr
      (fun hf => disjoint_left.mp hVavoid hx hf)
  have hlocal : (interior Db ∪ (c '' (A ×ˢ Ioo 0 δ))) ∩
      (K \ (c '' (A ×ˢ Ico 0 ε))) = Db := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxC⟩
      · exact interior_subset hx
      · obtain ⟨z, hz, rfl⟩ := hx
        have hge : ε ≤ z.2 := le_of_not_gt (fun h =>
          hxC.2 ⟨z, ⟨hz.1, hz.2.1.le, h⟩, rfl⟩)
        rcases eq_or_lt_of_le hge with ht | ht
        · exact b.boundary_subset ⟨z, ⟨hz.1, ht.symm⟩, rfl⟩
        · exact interior_subset (hVinside ⟨z, ⟨hz.1, ht, hz.2.2⟩, rfl⟩)
    · intro hxB
      refine ⟨?_, hBC hxB⟩
      by_cases hxS' : x ∈ c '' (A ×ˢ {ε})
      · exact Or.inr (hSO hxS')
      · left
        rw [b.interior_eq_sdiff]
        exact ⟨hxB, hxS'⟩
  let C : Set X := K \ (c '' (A ×ˢ Ico 0 ε))
  have hrelative : IsClopen ((Subtype.val : C → X) ⁻¹' Db) := by
    refine ⟨b.isCompact.isClosed.preimage continuous_subtype_val, ?_⟩
    have heq : (Subtype.val : C → X) ⁻¹' Db =
        (Subtype.val : C → X) ⁻¹' (interior Db ∪ (c '' (A ×ˢ Ioo 0 δ))) := by
      ext x
      constructor
      · intro hx
        exact (hlocal.symm.subset hx).1
      · intro hx
        exact hlocal.subset ⟨hx, x.property⟩
    rw [heq]
    exact (isOpen_interior.union hopen).preimage continuous_subtype_val
  have hnonempty : ((Subtype.val : C → X) ⁻¹' Db).Nonempty :=
    ⟨⟨c (z0, ε), hBC (b.boundary_subset hxS)⟩, b.boundary_subset hxS⟩
  let : ConnectedSpace C := isConnected_iff_connectedSpace.mp hC
  have hall := hrelative.eq_univ hnonempty
  apply Subset.antisymm hBC
  intro x hxC
  have h : (⟨x, hxC⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' Db := hall.symm ▸ mem_univ _
  exact h

end PoincareConjecture.M76.ChartwisePLBall
