import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedBlockFrontier

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

namespace OriginalDiskProduct

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {L : Set X} {j : V2 → X}

def capDisk (P : OriginalDiskProduct e L j) (b : Bool) : Set X :=
  P.map '' (D ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)})

def capRimSet (P : OriginalDiskProduct e L j) (b : Bool) : Set X :=
  P.map '' (Q ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)})

theorem cap_source_subset (b : Bool) :
    D ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)} ⊆ D ×ˢ Icc (-1 : ℝ) 1 := by
  rintro z ⟨hz, ht⟩
  refine ⟨hz, ?_⟩
  have heq : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := ht
  rw [heq]
  cases b <;> norm_num

theorem isCompact_capDisk (P : OriginalDiskProduct e L j) (b : Bool) :
    IsCompact (P.capDisk b) :=
  ((isCompact_closedBall (0 : V2) 1).prod isCompact_singleton).image_of_continuousOn
    (P.polyhedral.continuousOn.mono (cap_source_subset b))

theorem isConnected_capDisk (P : OriginalDiskProduct e L j) (b : Bool) :
    IsConnected (P.capDisk b) :=
  ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod isConnected_singleton).image
    P.map (P.polyhedral.continuousOn.mono (cap_source_subset b))

theorem disjoint_capDisks (P : OriginalDiskProduct e L j) (b : Bool) :
    Disjoint (P.capDisk b) (P.capDisk (!b)) := by
  apply disjoint_left.mpr
  rintro x ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
  have hzw := P.injective (cap_source_subset b hz) (cap_source_subset (!b) hw)
    (hx.trans hy.symm)
  have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
  have hu : w.2 = if !b then (1 / 2 : ℝ) else -(1 / 2) := hw.2
  have hh := congrArg Prod.snd hzw
  rw [ht, hu] at hh
  cases b <;> norm_num at hh

theorem capRimSet_subset_capDisk (P : OriginalDiskProduct e L j) (b : Bool) :
    P.capRimSet b ⊆ P.capDisk b :=
  image_mono (prod_mono sphere_subset_closedBall subset_rfl)

theorem endDisks_eq_capDisks (P : OriginalDiskProduct e L j) :
    P.endDisks = P.capDisk false ∪ P.capDisk true := by
  simp only [endDisks, capDisk, Bool.false_eq_true, ↓reduceIte]
  rw [← image_union, ← prod_union]
  rfl

theorem endDisks_subset_closedStrip (P : OriginalDiskProduct e L j) :
    P.endDisks ⊆ P.closedStrip := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
  have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := hz.2
  rcases ht with ht | ht <;> rw [ht] <;> norm_num

theorem compressed_frontier_inter_block (P : OriginalDiskProduct e L j)
    {F Fnew : Set X} (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks) :
    Fnew ∩ P.closedStrip = P.endDisks := by
  apply Subset.antisymm
  · rintro x ⟨hx, ⟨z, hz, rfl⟩⟩
    rcases hnew.subset hx with hold | hend
    · have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
        by_contra h
        push Not at h
        exact hold.2 ⟨z, ⟨hz.1,
          lt_of_le_of_ne hz.2.1 h.1.symm, lt_of_le_of_ne hz.2.2 h.2⟩, rfl⟩
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
    · exact hend
  · intro x hx
    exact ⟨hnew.symm.subset (Or.inr hx), P.endDisks_subset_closedStrip hx⟩

theorem capRimSet_subset_frontier_mark (P : OriginalDiskProduct e L j)
    {U F : Set X} (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U) (b : Bool) :
    P.capRimSet b ⊆ F := by
  rintro x ⟨z, hz, rfl⟩
  have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
  apply (P.protected_frontier_iff hcut hsmall z ?_).mpr hz.1
  refine ⟨sphere_subset_closedBall hz.1, ?_⟩
  rw [ht]
  cases b <;> norm_num

theorem cap_complement_subset_frontier_mark (P : OriginalDiskProduct e L j)
    {U F Fnew S : Set X} (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hS : S ⊆ Fnew) (b : Bool) (hopposite : Disjoint S (P.capDisk (!b))) :
    S \ (P.capDisk b \ P.capRimSet b) ⊆ F := by
  intro x hx
  have hcaps : P.endDisks = P.capDisk b ∪ P.capDisk (!b) := by
    rw [P.endDisks_eq_capDisks]
    cases b <;> simp [union_comm]
  rcases hnew.subset (hS hx.1) with hold | hcap
  · exact hold.1
  · rcases hcaps.subset hcap with hthis | hother
    · have hrim : x ∈ P.capRimSet b := by
        by_contra h
        exact hx.2 ⟨hthis, h⟩
      exact P.capRimSet_subset_frontier_mark hcut hsmall b hrim
    · exact False.elim (disjoint_left.mp hopposite hx.1 hother)

end OriginalDiskProduct

end PoincareConjecture.M76
