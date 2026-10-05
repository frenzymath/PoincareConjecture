import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.SquareShellHomeomorph

/-!
# Identity shells in a prescribed radial transport

When both source and target radii coincide, choose the literal
identity homeomorphism with its actual finite PL certificate.
This fixes an outer shell throughout its interior as required
for descent through torus quotient charts. See Hatcher p. 7,
Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace SquareShell

/-- Unchanged radius endpoints give the identity affine
radius map. See M76 derivation 270. -/
theorem radiusMap_self {a b : ℝ} (hab : a < b) (r : ℝ) :
    radiusMap a b a b r = r := by
  unfold radiusMap
  rw [div_self (sub_ne_zero.mpr hab.ne'), one_mul]
  ring

/-- Prescribed shell transport can be chosen to fix the
entire shell whenever its two radii remain unchanged. This
strengthens endpoint agreement to an actual fixed collar.
See Hatcher p. 7 and M76 derivation 270. -/
theorem exists_fixed_radius_homeomorph {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    ∃ H : shell a b ≃ₜ shell c d, H.IsFinitePL ∧
      (∀ x : shell a b,
        ‖(H x : ℝ × ℝ)‖ = radiusMap a b c d ‖(x : ℝ × ℝ)‖ ∧
        (‖(x : ℝ × ℝ)‖ = a → (H x : ℝ × ℝ) = (c / a) • (x : ℝ × ℝ)) ∧
        (‖(x : ℝ × ℝ)‖ = b → (H x : ℝ × ℝ) = (d / b) • (x : ℝ × ℝ))) ∧
      (a = c → b = d → ∀ x : shell a b, (H x : ℝ × ℝ) = x) := by
  by_cases hsame : a = c ∧ b = d
  · obtain ⟨hac, hbd⟩ := hsame
    subst c
    subst d
    obtain ⟨e, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ := exists_radius_homeomorph ha hab ha hab
    have href : (Homeomorph.refl (shell a b)).IsFinitePL :=
      ⟨id, ⟨K, hK, hKS, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ (ℝ × ℝ))⟩,
        fun _ => rfl⟩
    refine ⟨Homeomorph.refl _, href, ?_, fun _ _ _ => rfl⟩
    intro x
    change ‖(x : ℝ × ℝ)‖ = radiusMap a b a b ‖(x : ℝ × ℝ)‖ ∧ _
    rw [radiusMap_self hab]
    exact ⟨rfl, fun _ => by simp [div_self ha.ne'],
      fun _ => by simp [div_self (ha.trans hab).ne']⟩
  · obtain ⟨H, hH, hdata⟩ := exists_radius_homeomorph ha hab hc hcd
    exact ⟨H, hH, hdata, fun h₁ h₂ => False.elim (hsame ⟨h₁, h₂⟩)⟩

end SquareShell
