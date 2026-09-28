import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusProjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.CoordinateRimIntersection



set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem proper_annulus_image_inter_mark
    {X : Type*} [TopologicalSpace X] {R S₀ S₁ : Set X}
    (hS₀ : S₀ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (g : (V1 × V2) → X)
    (hproper : ∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hfalse : ∀ z : Q2, g (endpoint false, z) ∈ S₀)
    (htrue : ∀ z : Q2, g (endpoint true, z) ∈ S₁) :
    g '' source ∩ S₀ = range (fun z : Q2 => g (endpoint false, z)) := by
  apply Subset.antisymm
  · rintro x ⟨⟨y, hy, rfl⟩, hx⟩
    obtain ⟨b, hb⟩ := (mem_sphere_iff_exists_endpoint y.1).mp
      ((hproper ⟨y, hy⟩).mp (hS₀ hx))
    have hpair : y = (endpoint b, y.2) := Prod.ext hb rfl
    cases b
    · exact ⟨⟨y.2, hy.2⟩, congrArg g hpair.symm⟩
    · exfalso
      apply disjoint_left.mp hdis hx
      rw [hpair]
      exact htrue ⟨y.2, hy.2⟩
  · rintro x ⟨z, rfl⟩
    exact ⟨⟨(endpoint false, z),
      ⟨sphere_subset_closedBall (endpoint_mem_sphere false), z.property⟩, rfl⟩, hfalse z⟩

theorem proper_annuli_intersection_on_mark
    {X : Type*} [TopologicalSpace X] {R S₀ S₁ : Set X}
    (hS₀ : S₀ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (g : Bool → (V1 × V2) → X)
    (hproper : ∀ b, ∀ x : source,
      g b x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hfalse : ∀ b (z : Q2), g b (endpoint false, z) ∈ S₀)
    (htrue : ∀ b (z : Q2), g b (endpoint true, z) ∈ S₁) :
    (g false '' source ∩ g true '' source) ∩ S₀ =
      range (fun z : Q2 => g false (endpoint false, z)) ∩
        range (fun z : Q2 => g true (endpoint false, z)) := by
  rw [← proper_annulus_image_inter_mark hS₀ hdis (g false)
    (hproper false) (hfalse false) (htrue false),
    ← proper_annulus_image_inter_mark hS₀ hdis (g true)
      (hproper true) (hfalse true) (htrue true)]
  ext x
  simp only [mem_inter_iff]
  tauto

theorem coordinate_proper_annuli_intersection_on_mark
    {C X : Type*} [TopologicalSpace C] [TopologicalSpace X] {R S₀ S₁ : Set X}
    (hS₀ : S₀ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (h : (C × C) ≃ₜ S₀) (q : Bool → Q2 ≃ₜ C) (a : C)
    (g : Bool → (V1 × V2) → X)
    (hproper : ∀ b, ∀ x : source,
      g b x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hfalse : ∀ z : Q2, g false (endpoint false, z) = (h (q false z, a) : X))
    (htrue : ∀ z : Q2, g true (endpoint false, z) = (h (a, q true z) : X))
    (hother : ∀ b (z : Q2), g b (endpoint true, z) ∈ S₁) :
    (g false '' source ∩ g true '' source) ∩ S₀ = {(h (a, a) : X)} := by
  have hmarked (b : Bool) (z : Q2) : g b (endpoint false, z) ∈ S₀ := by
    cases b
    · rw [hfalse]
      exact (h _).property
    · rw [htrue]
      exact (h _).property
  rw [proper_annuli_intersection_on_mark hS₀ hdis g hproper hmarked hother]
  exact (coordinate_rim_intersection h q a
    (fun b z => g b (endpoint false, z)) hfalse htrue).1

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
