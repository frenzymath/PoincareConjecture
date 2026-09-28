import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.PolyhedralSource
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.MarkedAnnulusApproximation

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_marked_PL_annulus_of_commensurable
    {E₀ E₁ X ι : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hFclopen : ∀ b, IsClopen ((Subtype.val : frontier R → X) ⁻¹' F b))
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (hi₀ : ∀ x, (i₀ x : X) ∈ F false) (hi₁ : ∀ x, (i₁ x : X) ∈ F true)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (alpha : Path e₀ e₀) :
    ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path e₁ e₁) (g : (V1 × V2) → X)
      (gamma gamma₀ : ∀ b, C(Q2, F b)),
      PolyhedralPLInCharts e g source ∧ MapsTo g source R ∧
      (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
      (∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b))) ∧
      (∀ s : unitInterval, (gamma false (squareRimLoop s) : X) =
        (i₀ (boundaryLoopIterate alpha n s) : X)) ∧
      (∀ s : unitInterval, (gamma true (squareRimLoop s) : X) = (i₁ (beta s) : X)) := by
  obtain ⟨n, hn, beta, f, hf₀, hf₁⟩ :=
    exists_polyhedral_source_singular_annulus i₀ i₁ e₀ e₁ k hc alpha
  let inc (b : Bool) : C(Q2, source) :=
    ⟨fun u => ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
  have hinc₀ (u : Q2) : inc false u = cylinder (0, u) := (cylinder_zero u).symm
  have hinc₁ (u : Q2) : inc true u = cylinder (1, u) := (cylinder_one u).symm
  have hfF (b : Bool) (u : Q2) : (f (inc b u) : X) ∈ F b := by
    obtain ⟨s, rfl⟩ := surjective_squareRimLoop u
    cases b
    · rw [hinc₀, hf₀]
      exact hi₀ _
    · rw [hinc₁, hf₁]
      exact hi₁ _
  let gamma (b : Bool) : C(Q2, F b) :=
    ⟨fun u => ⟨f (inc b u), hfF b u⟩,
      (continuous_subtype_val.comp (f.continuous.comp (inc b).continuous)).subtype_mk _⟩
  obtain ⟨g, a, hg, hga, gamma₀, hrim, hhom⟩ :=
    exists_marked_PL_annulus_pair he F hF hFclopen f gamma (fun _ _ => rfl)
  refine ⟨n, hn, beta, g, gamma, gamma₀, hg, ?_, hrim, hhom, ?_, ?_⟩
  · intro x hx
    rw [hga ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property
  · intro s
    change (f (inc false (squareRimLoop s)) : X) = _
    rw [hinc₀, hf₀]
  · intro s
    change (f (inc true (squareRimLoop s)) : X) = _
    rw [hinc₁, hf₁]

end PoincareConjecture.M76
