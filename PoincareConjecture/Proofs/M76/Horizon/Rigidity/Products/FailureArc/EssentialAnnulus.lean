import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.RimEssentiality









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

def sourceAnnulusRim {X : Type*} [TopologicalSpace X]
    (f : C(source, X)) (b : Bool) : C(Q2, X) :=
  f.comp ⟨fun u => ⟨(endpoint b, u),
    sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

noncomputable def sourceAnnulusRimHomotopy {X : Type*} [TopologicalSpace X]
    (f : C(source, X)) : (sourceAnnulusRim f false).Homotopy (sourceAnnulusRim f true) where
  toContinuousMap := f.comp ⟨cylinder, cylinder.continuous⟩
  map_zero_left := by intro u; change f (cylinder (0, u)) = _; rw [cylinder_zero]; rfl
  map_one_left := by intro u; change f (cylinder (1, u)) = _; rw [cylinder_one]; rfl



theorem exists_essential_marked_PL_annulus_of_commensurable
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
    (hinj : Function.Injective (FundamentalGroup.map i₀ e₀))
    (alpha : Path e₀ e₀)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0) :
    ∃ (g : (V1 × V2) → X) (f : C(source, R)),
      PolyhedralPLInCharts e g source ∧
      (∀ x : source, g x = (f x : X)) ∧
      (∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ F b) ∧
      (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
      ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path e₁ e₁) (gamma gamma₀ : ∀ b, C(Q2, F b)),
        (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
        (∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b))) ∧
        (∀ s : unitInterval, (gamma false (squareRimLoop s) : X) =
          (i₀ (boundaryLoopIterate alpha n s) : X)) ∧
        (∀ s : unitInterval, (gamma true (squareRimLoop s) : X) = (i₁ (beta s) : X)) := by
  obtain ⟨n, hn, beta, g, gamma, gamma₀, hg, hgR, hrim, hhom, hleft, hright⟩ :=
    exists_marked_PL_annulus_of_commensurable he F hF hFclopen
      i₀ i₁ hi₀ hi₁ e₀ e₁ k hc alpha
  let f : C(source, R) :=
    ⟨fun x => ⟨g x, hgR x.property⟩, hg.continuousOn.domRestrict.subtype_mk _⟩
  let inc (b : Bool) : C(F b, R) :=
    ContinuousMap.inclusion ((hF b).trans he.closed.frontier_subset)
  have hnegative : ¬ (sourceAnnulusRim f false).Nullhomotopic := by
    have heq : (inc false).comp (gamma₀ false) = sourceAnnulusRim f false := by
      ext u
      exact (hrim false u).symm
    rw [← heq]
    apply not_nullhomotopic_of_boundary_power_homotopy i₀ e₀ hinj alpha ha n hn
      ((inc false).comp (gamma false)) ((inc false).comp (gamma₀ false))
      (fun s => Subtype.ext (hleft s))
    exact (ContinuousMap.Homotopic.refl (inc false)).comp (hhom false)
  have hessential (b : Bool) : ¬ (sourceAnnulusRim f b).Nullhomotopic := by
    cases b
    · exact hnegative
    · rintro ⟨y, hy⟩
      exact hnegative ⟨y, ContinuousMap.Homotopic.trans ⟨sourceAnnulusRimHomotopy f⟩ hy⟩
  refine ⟨g, f, hg, fun _ => rfl, ?_, hessential,
    n, hn, beta, gamma, gamma₀, hrim, hhom, hleft, hright⟩
  intro b u
  rw [hrim]
  exact (gamma₀ b u).property

end PoincareConjecture.M76
