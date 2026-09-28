import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SingularAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_square_cylinder_of_closed_curves
    {X : Type*} [TopologicalSpace X]
    (H : C(unitInterval × unitInterval, X)) (hclosed : ∀ t, H (t, 0) = H (t, 1)) :
    ∃ F : C(unitInterval × Q2, X),
      ∀ t s : unitInterval, F (t, squareRimLoop s) = H (t, s) := by
  let flip : C(unitInterval × unitInterval, X) := H.comp ⟨Prod.swap, continuous_swap⟩
  let p : Path (flip.curry 0) (flip.curry 0) :=
    { toFun := flip.curry
      continuous_toFun := flip.curry.continuous
      source' := rfl
      target' := by
        apply ContinuousMap.ext
        intro t
        exact (hclosed t).symm }
  obtain ⟨g, hg⟩ := exists_squareRimMap p
  refine ⟨g.uncurry.comp ⟨Prod.swap, continuous_swap⟩, ?_⟩
  intro t s
  change g (squareRimLoop s) t = H (t, s)
  rw [hg]
  rfl

theorem exists_polyhedral_source_singular_annulus
    {E₀ E₁ X : Type*}
    [TopologicalSpace E₀] [TopologicalSpace E₁] [TopologicalSpace X]
    (i₀ : C(E₀, X)) (i₁ : C(E₁, X)) (e₀ : E₀) (e₁ : E₁)
    (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (alpha : Path e₀ e₀) :
    ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path e₁ e₁) (f : C(source, X)),
      (∀ s : unitInterval, f (cylinder (0, squareRimLoop s)) =
        i₀ (boundaryLoopIterate alpha n s)) ∧
      (∀ s : unitInterval, f (cylinder (1, squareRimLoop s)) = i₁ (beta s)) := by
  obtain ⟨n, hn, beta, hbeta⟩ :=
    exists_boundary_loop_power_homotopy i₀ i₁ e₀ e₁ k hc alpha
  obtain ⟨H⟩ := exists_closed_curve_homotopy_of_conjugate
    ((boundaryLoopIterate alpha n).map i₀.continuous) (beta.map i₁.continuous) k hbeta
  obtain ⟨F, hF⟩ := exists_square_cylinder_of_closed_curves H.toHomotopy.toContinuousMap
    (fun t => H.prop t)
  let f : C(source, X) := F.comp ⟨cylinder.symm, cylinder.symm.continuous⟩
  refine ⟨n, hn, beta, f, ?_, ?_⟩
  · intro s
    change F (cylinder.symm (cylinder (0, squareRimLoop s))) = _
    rw [cylinder.symm_apply_apply, hF]
    exact H.apply_zero s
  · intro s
    change F (cylinder.symm (cylinder (1, squareRimLoop s))) = _
    rw [cylinder.symm_apply_apply, hF]
    exact H.apply_one s

end PoincareConjecture.M76
