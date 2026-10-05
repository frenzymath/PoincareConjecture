import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Arcs.RelativeProperArcExtension

/-!
# A protected rim-fixed arc move and its local avoidance consequence

The proper-arc extension is the bounded local part of the same-edge
move.  This file exposes the exact consequence needed by the later
ambient step: if the replacement arc misses a retained sphere set,
then the inverse motion has no selected-edge contact with that set.
The replacement arc itself and the extension outside the disk remain
separate P3a obligations.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Extend a prescribed finite-PL proper-arc replacement while fixing
the complete disk rim, and record the exact avoidance statement for
the inverse motion.  No replacement arc or ambient extension is
constructed here; both are explicit inputs to this local consumer.
See PrimeReduction derivation021 and Kneser1929 p.254. -/
theorem exists_protected_rim_fixed_arc_move
    {s q w W : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ q) (hb : b ∈ q)
    (hproper : w \ {a, b} ⊆ s \ q)
    (hReplacement : W \ {a, b} ⊆ s \ q)
    (e : w ≃ₜ W) (he : e.IsFinitePL)
    (hfix : ∀ x : w, (x : E) ∈ ({a, b} : Set E) → (e x : E) = x)
    {sphereSet : Set E} (havoid : Disjoint W sphereSet) :
    ∃ H : s ≃ₜ s, H.IsFinitePL ∧
      (∀ (x : w) (hx : (x : E) ∈ s),
        (H ⟨x, hx⟩ : E) = e x) ∧
      (∀ x : s, (x : E) ∈ q → H x = x) ∧
      (∀ x : s, (x : E) ∈ w ↔ (H x : E) ∈ W) ∧
      (∀ y : s, (y : E) ∈ sphereSet →
        (H.symm y : E) ∉ w) := by
  obtain ⟨H, hH, hmap, hq, hiff⟩ :=
    hs.exists_extension_of_proper_arc_fix_boundary hw hW hab ha hb
      hproper hReplacement e he hfix
  refine ⟨H, hH, hmap, hq, hiff, ?_⟩
  intro y hySphere hyw
  have hyW : (H (H.symm y) : E) ∈ W :=
    (hiff (H.symm y)).mp hyw
  have hyW' : (y : E) ∈ W := by
    rw [← congrArg Subtype.val (H.apply_symm_apply y)]
    exact hyW
  exact Set.disjoint_left.mp havoid hyW' hySphere

end PoincareMT.M76
