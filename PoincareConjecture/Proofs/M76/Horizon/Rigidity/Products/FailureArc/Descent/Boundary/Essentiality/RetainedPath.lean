import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.Selection

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem exists_spanning_retained_rim_path
    {X : Type*} [TopologicalSpace X] {R : Set X} {K Q : Set P2}
    (c : Bool → P2 → P2) (sign : Bool → Bool) (H : Sq ≃ₜ K)
    (hHQ : ∀ z : Sq, (H z : P2) ∈ Q ↔ (z : P2).2 = 0)
    (hleft : ∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (sign false)))
    (hright : ∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (sign true)))
    (old : P2 → X) (hold : ContinuousOn old Q) (holdR : MapsTo old Q R)
    (τ : C3 → X) (hτ : ContinuousOn τ tube) (hτR : MapsTo τ tube R)
    (h0 : ∀ p ∈ source, old (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, old (c true p) = τ ((p.2, -p.2), p.1)) :
    ∃ A : Path (spanningEndMap τ hτ hτR (spanningEndPoint false (sign false)))
      (spanningEndMap τ hτ hτR (spanningEndPoint true (sign true))),
      ∀ t : I, (A t : X) = old (H ⟨(t, 0), t.property, by norm_num⟩) := by
  have hfar (i : Bool) : (0, farArmParameter (sign i)) ∈ source :=
    arm_far_subset_source (sign i) ⟨by norm_num, rfl⟩
  let A : Path (spanningEndMap τ hτ hτR (spanningEndPoint false (sign false)))
      (spanningEndMap τ hτ hτR (spanningEndPoint true (sign true))) :=
    { toFun t := ⟨old (H ⟨(t, 0), t.property, by norm_num⟩), holdR ((hHQ _).mpr rfl)⟩
      continuous_toFun := (hold.comp_continuous
        (continuous_subtype_val.comp (H.continuous.comp (by fun_prop)))
          (fun _ ↦ (hHQ _).mpr rfl)).subtype_mk _
      source' := Subtype.ext ((congrArg old (hleft 0)).trans (h0 _ (hfar false)))
      target' := Subtype.ext ((congrArg old (hright 0)).trans (h1 _ (hfar true))) }
  exact ⟨A, fun _ ↦ rfl⟩

end PoincareConjecture.M76.Dehn
