import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.OpenProperDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.ChartTransport
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.ChartImage

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem chart_image_frontier_iff
    {X : Type*} [TopologicalSpace X]
    (a : OpenPartialHomeomorph X V3) (U : TopologicalSpace.Opens V3)
    (hU : Nonempty U) (hUT : (U : Set V3) ⊆ a.target) (R : Set X) (y : U) :
    a.symm (y : V3) ∈ frontier R ↔
      (y : V3) ∈ frontier ((Subtype.val : U → V3) '' {z : U | a.symm (z : V3) ∈ R}) := by
  have hopen : IsOpenMap (Subtype.val : U → V3) := U.isOpen.isOpenMap_subtype_val
  have hpre := hopen.preimage_frontier_eq_frontier_preimage
    (continuous_subtype_val : Continuous (Subtype.val : U → V3))
    ((Subtype.val : U → V3) '' {z : U | a.symm (z : V3) ∈ R})
  have heq : (Subtype.val : U → V3) ⁻¹'
      ((Subtype.val : U → V3) '' {z : U | a.symm (z : V3) ∈ R}) =
      {z : U | a.symm (z : V3) ∈ R} :=
    preimage_image_eq _ Subtype.val_injective
  rw [heq, frontier_chart_image_eq a U hU hUT R] at hpre
  exact (Set.ext_iff.mp hpre y).symm



theorem exists_proper_disk_in_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (i : ι) (U : TopologicalSpace.Opens V3) (hU : Nonempty U)
    (hUT : (U : Set V3) ⊆ (e i).target)
    {S : Set V3} (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL)
    (f : C(D2, {y : U | (e i).symm (y : V3) ∈ R}))
    (hboundary : ∀ x : Q2,
      ((f ⟨x, sphere_subset_closedBall x.property⟩ : U) : V3) = (gamma x : V3))
    (hfront : ∀ x : Q2, (e i).symm (gamma x) ∈ frontier R) :
    ∃ (D : Set X) (b : D2 ≃ₜ D) (j : V2 → X),
      IsCompact D ∧ D ⊆ R ∩ ((e i).symm '' (U : Set V3)) ∧
      PolyhedralPLInCharts e j D2 ∧ (∀ x : D2, j x = (b x : X)) ∧
      (∀ x : Q2, (b ⟨x, sphere_subset_closedBall x.property⟩ : X) =
        (e i).symm (gamma x)) ∧
      ∀ x : D2, (b x : X) ∈ frontier R ↔ (x : V2) ∈ Q2 := by
  let C : Set U := {y | (e i).symm (y : V3) ∈ R}
  have hS : S ⊆ frontier ((Subtype.val : U → V3) '' C) := by
    intro z hz
    let q := gamma.symm ⟨z, hz⟩
    let y : U := f ⟨q, sphere_subset_closedBall q.property⟩
    have hy : (y : V3) = z := (hboundary q).trans
      (congrArg Subtype.val (gamma.apply_symm_apply ⟨z, hz⟩))
    rw [← hy]
    apply (chart_image_frontier_iff (e i) U hU hUT R y).mp
    change (e i).symm ((f ⟨q, sphere_subset_closedBall q.property⟩ : U) : V3) ∈ frontier R
    rw [hboundary]
    exact hfront q
  obtain ⟨D0, b0, _, hD0, hb0, hbvalues, hbproper⟩ :=
    exists_proper_disk_in_open_ambient U hU (he.chart_image i U hU hUT)
      hS gamma hgamma f hboundary
  have hD0U : D0 ⊆ (U : Set V3) := by
    rintro z hz
    obtain ⟨y, _, rfl⟩ := hD0 hz
    exact y.property
  obtain ⟨b, j, hj, hjb, hbcoord, _, hcompact, _⟩ :=
    exists_chartwise_disk_transport e i b0 hb0 (hD0U.trans hUT)
  refine ⟨(e i).symm '' D0, b, j, hcompact, ?_, hj, hjb, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hD0 hy
    exact ⟨hwv ▸ hw, ⟨y, hD0U hy, rfl⟩⟩
  · intro x
    rw [hbcoord, hbvalues]
  · intro x
    rw [hbcoord]
    exact (chart_image_frontier_iff (e i) U hU hUT R
      ⟨b0 x, hD0U (b0 x).property⟩).trans (hbproper x)

end PoincareConjecture.M76.Dehn
