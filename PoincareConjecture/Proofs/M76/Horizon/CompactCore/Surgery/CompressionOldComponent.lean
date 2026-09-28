import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedBlockFrontier
import Mathlib.Analysis.Normed.Module.Connected











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}

theorem frontier_mark_inter_closedStrip (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U) :
    F ∩ P.closedStrip = P.map '' (Q ×ˢ J) := by
  ext y
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact ⟨z, ⟨(P.protected_frontier_iff hcut hsmall z hzfull).mp hy, hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨sphere_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact ⟨(P.protected_frontier_iff hcut hsmall z hzfull).mpr hz.1,
      z, ⟨sphere_subset_closedBall hz.1, hz.2⟩, rfl⟩

theorem isCompact_frontier_mark_inter_closedStrip (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U) :
    IsCompact (F ∩ P.closedStrip) := by
  rw [P.frontier_mark_inter_closedStrip hcut hsmall]
  apply ((isCompact_sphere (0 : V2) 1).prod isCompact_Icc).image_of_continuousOn
  apply P.polyhedral.continuousOn.mono
  intro z hz
  exact ⟨sphere_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem isConnected_frontier_mark_inter_closedStrip (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U) :
    IsConnected (F ∩ P.closedStrip) := by
  rw [P.frontier_mark_inter_closedStrip hcut hsmall]
  apply ((isConnected_sphere (by simp) (0 : V2) zero_le_one).prod
    (isConnected_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2))).image
  apply P.polyhedral.continuousOn.mono
  intro z hz
  exact ⟨sphere_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem central_rim_subset_frontier_mark_inter_closedStrip (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U) :
    j '' Q ⊆ F ∩ P.closedStrip := by
  rw [P.frontier_mark_inter_closedStrip hcut hsmall]
  rintro y ⟨z, hz, rfl⟩
  exact ⟨(z, 0), ⟨hz, by norm_num⟩, P.central z (sphere_subset_closedBall hz)⟩

theorem exists_old_component_label (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    {n : ℕ} (S : Fin n → Set X) (hcover : (⋃ i, S i) = F)
    (hcomponents : ∀ i, ∀ y ∈ S i, connectedComponentIn F y = S i)
    (hdisjoint : Pairwise fun i k => Disjoint (S i) (S k)) :
    ∃ c : Fin n,
      IsCompact (F ∩ P.closedStrip) ∧ IsConnected (F ∩ P.closedStrip) ∧
      (F ∩ P.closedStrip).Nonempty ∧ F ∩ P.closedStrip ⊆ S c ∧
      (∀ i, F ∩ P.closedStrip ⊆ S i ↔ c = i) ∧
      (∀ i, i ≠ c → Disjoint (S i) P.closedStrip) ∧
      j '' Q ⊆ S c ∧ ∀ u : Q, connectedComponentIn F (j u) = S c := by
  have hconn := P.isConnected_frontier_mark_inter_closedStrip hcut hsmall
  obtain ⟨y, hy⟩ := hconn.nonempty
  obtain ⟨c, hcy⟩ := mem_iUnion.mp (hcover.symm.subset hy.1)
  have hsub : F ∩ P.closedStrip ⊆ S c :=
    (hconn.isPreconnected.subset_connectedComponentIn hy inter_subset_left).trans
      (hcomponents c y hcy).subset
  have hrim : j '' Q ⊆ S c :=
    (P.central_rim_subset_frontier_mark_inter_closedStrip hcut hsmall).trans hsub
  refine ⟨c, P.isCompact_frontier_mark_inter_closedStrip hcut hsmall,
    hconn, hconn.nonempty, hsub, ?_, ?_, hrim, ?_⟩
  · intro i
    constructor
    · intro hi
      by_contra hne
      exact disjoint_left.mp (hdisjoint hne) (hsub hy) (hi hy)
    · intro hi
      exact hi ▸ hsub
  · intro i hic
    apply disjoint_left.mpr
    intro z hzi hzstrip
    have hzF : z ∈ F := hcover.subset (mem_iUnion.mpr ⟨i, hzi⟩)
    exact disjoint_left.mp (hdisjoint hic) hzi (hsub ⟨hzF, hzstrip⟩)
  · intro u
    exact hcomponents c (j u) (hrim ⟨u, u.property, rfl⟩)

end PoincareConjecture.M76.OriginalDiskProduct
