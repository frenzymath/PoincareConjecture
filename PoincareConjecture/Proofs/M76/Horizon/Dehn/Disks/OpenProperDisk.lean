import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.StandardProperDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.OpenStandardSubdomain

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_proper_disk_in_open_ambient
    (U : TopologicalSpace.Opens V3) (hU : Nonempty U) {R : Set U}
    (he : PLDomain (fun _ : Unit ↦ U.openPartialHomeomorphSubtypeCoe hU) R)
    {S : Set V3} (hS : S ⊆ frontier ((Subtype.val : U → V3) '' R))
    (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL)
    (f : C(D2, R))
    (hboundary : ∀ x : Q2,
      ((f ⟨x, sphere_subset_closedBall x.property⟩ : U) : V3) = (gamma x : V3)) :
    ∃ (D : Set V3) (b : D2 ≃ₜ D),
      IsCompact D ∧ D ⊆ (Subtype.val : U → V3) '' R ∧ b.IsFinitePL ∧
      (∀ x : Q2, (b ⟨x, sphere_subset_closedBall x.property⟩ : V3) = (gamma x : V3)) ∧
      ∀ x : D2, (b x : V3) ∈ frontier ((Subtype.val : U → V3) '' R) ↔
        (x : V2) ∈ Q2 := by
  let A : Set U := range (fun x : D2 ↦ (f x : U))
  have hA : IsCompact A := isCompact_range (continuous_subtype_val.comp f.continuous)
  have hAR : A ⊆ R := by
    rintro x ⟨y, rfl⟩
    exact (f y).property
  obtain ⟨K, V, hK, hKPL, hAK, hKR, _, hAV, _, _, hfront⟩ :=
    exists_compact_standard_subdomain_in_open U hU he hA hAR isOpen_univ
      (subset_univ _)
  have hSA : S ⊆ (Subtype.val : U → V3) '' A := by
    intro z hz
    let x := gamma.symm ⟨z, hz⟩
    refine ⟨f ⟨x, sphere_subset_closedBall x.property⟩, ?_, ?_⟩
    · exact ⟨⟨x, sphere_subset_closedBall x.property⟩, rfl⟩
    · exact (hboundary x).trans (congrArg Subtype.val (gamma.apply_symm_apply ⟨z, hz⟩))
  have hSK : S ⊆ frontier K := by
    intro z hz
    exact (hfront.symm.subset ⟨hS hz, hAV (hSA hz)⟩).1
  let fK : C(D2, K) :=
    ⟨fun x ↦ ⟨((f x : U) : V3), hAK ⟨f x, ⟨x, rfl⟩, rfl⟩⟩,
      (continuous_subtype_val.comp (continuous_subtype_val.comp f.continuous)).subtype_mk _⟩
  obtain ⟨D, b, hD, hDK, hb, hbvalues, hbproper⟩ :=
    exists_standard_proper_disk hK hKPL hSK gamma hgamma fK hboundary
  have hKR' : K ⊆ (Subtype.val : U → V3) '' R := hKR.trans inter_subset_left
  refine ⟨D, b, hD, hDK.trans hKR', hb, hbvalues, ?_⟩
  intro x
  constructor
  · intro hx
    apply (hbproper x).mp
    refine ⟨hK.isClosed.closure_eq.symm ▸ hDK (b x).property, ?_⟩
    intro hxint
    exact hx.2 (interior_mono hKR' hxint)
  · intro hx
    have hvalue := hbvalues ⟨x, hx⟩
    change (b x : V3) = (gamma ⟨x, hx⟩ : V3) at hvalue
    rw [hvalue]
    exact hS (gamma ⟨x, hx⟩).property

end PoincareConjecture.M76.Dehn
