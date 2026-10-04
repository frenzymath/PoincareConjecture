import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BallModelBoundaryExtension
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Prescribed boundary homeomorphisms of convex bodies extend

Gauge-rescaling models identify both a compact convex body and its
frontier with the unit ball and sphere. Radial extension conjugated
through these models retains the prescribed boundary map exactly.
See Hamilton pp. 66--68, Erickson pp. 8--10 and M76 derivation 115.
-/

set_option autoImplicit false

open Set Metric

/-- A compact convex body with nonempty interior has compatible
closed-ball and sphere models, respecting its boundary inclusion.
See M76 derivation 115. -/
theorem IsCompact.exists_compatible_unitBall_models {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (hs : IsCompact s) (hcv : Convex ℝ s) (hne : (interior s).Nonempty) :
    ∃ (h : s ≃ₜ closedBall (0 : E) 1) (hb : frontier s ≃ₜ sphere (0 : E) 1),
      ∀ x : frontier s, h ⟨x, hs.isClosed.frontier_subset x.property⟩ =
        ⟨hb x, sphere_subset_closedBall (hb x).property⟩ := by
  obtain ⟨e, _, he, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcv hne hs.isBounded
  rw [hs.isClosed.closure_eq] at he
  let h := (e.image s).trans (Homeomorph.setCongr he)
  let hb := (e.image (frontier s)).trans (Homeomorph.setCongr hfront)
  refine ⟨h, hb, ?_⟩
  intro x
  apply Subtype.ext
  rfl

/-- Any homeomorphism of the frontiers of two compact convex
bodies with nonempty interiors extends over the bodies. Properness
is used for radial quotient coordinates. See M76 derivation 115. -/
theorem Homeomorph.exists_convex_body_extension {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] [Nontrivial F]
    {s : Set E} {t : Set F} (hs : IsCompact s) (ht : IsCompact t)
    (hscv : Convex ℝ s) (htcv : Convex ℝ t)
    (hsne : (interior s).Nonempty) (htne : (interior t).Nonempty)
    (e : frontier s ≃ₜ frontier t) :
    ∃ f : s ≃ₜ t, ∀ x : frontier s,
      f ⟨x, hs.isClosed.frontier_subset x.property⟩ =
        ⟨e x, ht.isClosed.frontier_subset (e x).property⟩ := by
  obtain ⟨hX, hA, hXA⟩ := hs.exists_compatible_unitBall_models hscv hsne
  obtain ⟨hY, hB, hYB⟩ := ht.exists_compatible_unitBall_models htcv htne
  exact Homeomorph.exists_extension_of_unitBall_models
    (fun x => ⟨x, hs.isClosed.frontier_subset x.property⟩)
    (fun y => ⟨y, ht.isClosed.frontier_subset y.property⟩) hX hY hA hB hXA hYB e
