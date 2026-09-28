import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProtectedBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims











set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)

theorem mem_sphere_iff_exists_endpoint (x : V1) :
    x ∈ sphere (0 : V1) 1 ↔ ∃ b : Bool, x = endpoint b := by
  constructor
  · intro hx
    have hc : x = fun _ ↦ x 0 := funext fun i ↦ congrArg x (Subsingleton.elim i 0)
    have hn : |x 0| = 1 := by
      have hn := mem_sphere_zero_iff_norm.mp hx
      rw [hc, pi_norm_const, Real.norm_eq_abs] at hn
      exact hn
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with hp | hn
    · refine ⟨true, funext fun i ↦ ?_⟩
      exact (congrFun hc i).trans hp
    · refine ⟨false, funext fun i ↦ ?_⟩
      exact (congrFun hc i).trans hn
  · rintro ⟨b, rfl⟩
    exact endpoint_mem_sphere b



theorem injOn_boundary_of_rims {X : Type*} (g : (V1 × V2) → X)
    (hinj : ∀ b : Bool, Function.Injective
      (fun u : sphere (0 : V2) 1 ↦ g (endpoint b, u)))
    (hdis : Disjoint (range (fun u : sphere (0 : V2) 1 ↦ g (endpoint false, u)))
      (range (fun u : sphere (0 : V2) 1 ↦ g (endpoint true, u)))) :
    InjOn g (sphere (0 : V1) 1 ×ˢ sphere (0 : V2) 1) := by
  rintro ⟨a, u⟩ ⟨ha, hu⟩ ⟨b, v⟩ ⟨hb, hv⟩ heq
  obtain ⟨i, rfl⟩ := (mem_sphere_iff_exists_endpoint a).mp ha
  obtain ⟨k, rfl⟩ := (mem_sphere_iff_exists_endpoint b).mp hb
  have hik : i = k := by
    cases i <;> cases k
    · rfl
    · exact False.elim (disjoint_left.mp hdis ⟨⟨u, hu⟩, rfl⟩ ⟨⟨v, hv⟩, heq.symm⟩)
    · exact False.elim (disjoint_left.mp hdis ⟨⟨v, hv⟩, rfl⟩ ⟨⟨u, hu⟩, heq⟩)
    · rfl
  subst k
  exact Prod.ext rfl (congrArg Subtype.val (hinj i (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) heq))

end PoincareConjecture.M76.Dehn.ProtectedAnnulus

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
  {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}




theorem Step.exists_annulus_projection_neighborhood (step : Step s t)
    (hS : S.space = ProtectedAnnulus.source) (hSf : S.faces.Finite)
    {j : (V1 × V2) → t.Carrier} (hj : PolyhedralPLInCharts t.charts j S.space)
    (hji : IsEmbedding (fun x : S.space ↦ j x)) (R : Set M)
    (hproper : ∀ x ∈ S.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Q)
    (hvalues : ∀ (b : Bool) (u : sphere (0 : V2) 1),
      j (endpoint b, u) = t.annulusRim hS b u)
    (hinj : ∀ b : Bool, Function.Injective
      (fun u : sphere (0 : V2) 1 ↦ f (endpoint b, u)))
    (hdis : Disjoint (range (fun u : sphere (0 : V2) 1 ↦ f (endpoint false, u)))
      (range (fun u : sphere (0 : V2) 1 ↦ f (endpoint true, u)))) :
    let p := (step.projection ∘ step.inclusion) ∘ j
    (∀ (b : Bool) (u : sphere (0 : V2) 1), p (endpoint b, u) = s.annulusRim hS b u) ∧
    ∃ (D : SimplicialComplex ℝ (V1 × V2)) (O : Set s.Carrier) (ε : ℝ),
      D.faces.Finite ∧ D.space = doubleLocusOn p S.space ∧
      IsCompact D.space ∧ D.space ⊆ S.space ∧ Disjoint D.space Q ∧
      IsOpen O ∧ p '' Q ⊆ O ∧ 0 < ε ∧ cthickening ε Q ⊆ D.spaceᶜ ∧
      S.space ∩ p ⁻¹' O = S.space \ D.space ∧
      InjOn p (S.space \ D.space) ∧
      (∀ x ∈ S.space, x ∈ cthickening ε Q →
        ∀ y ∈ S.space, p x = p y → x = y) := by
  dsimp only
  have hQK : Q ⊆ S.space := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    exact hS.symm.subset ⟨sphere_subset_closedBall hx, hu⟩
  have hwhole : EqOn (t.projection ∘ j) f Q := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    obtain ⟨b, rfl⟩ := (mem_sphere_iff_exists_endpoint x).mp hx
    change t.projection (j (endpoint b, u)) = _
    rw [hvalues b ⟨u, hu⟩, t.annulusRim_projection hS]
  constructor
  · intro b u
    change step.projection (step.inclusion (j (endpoint b, u))) = _
    rw [hvalues b u]
    exact step.source_eq _ (hS.symm.subset
      ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩)
  · apply step.exists_protected_boundary_projection S hSf hj hji Q
      ((isCompact_sphere (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1)) hQK R hproper
    intro x hx y hy heq
    apply injOn_boundary_of_rims f hinj hdis hx hy
    rw [← hwhole hx, ← hwhole hy]
    exact heq

end Geometry.OriginalPLTower
