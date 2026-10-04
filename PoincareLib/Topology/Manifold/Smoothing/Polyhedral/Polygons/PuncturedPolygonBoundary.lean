import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonComplementComponents
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.PuncturedCircle
import Mathlib.Topology.Perfect

/-!
# Punctured polygon boundaries

Removing one point from a simple polygon boundary leaves a
connected set dense in the full boundary. This permits the
exceptional curves of Alexander 1924, p. 7 to touch at their
distinguished point; see M76 derivation 151.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

/-- A simple polygon boundary remains nonempty and connected
after deleting any one ambient point. See Alexander p. 7 and
M76 derivation 151. -/
theorem isConnected_boundary_sdiff_singleton (q : ℝ × ℝ) :
    IsConnected (P.boundary ℝ \ {q}) := by
  classical
  by_cases hq : q ∈ P.boundary ℝ
  · obtain ⟨e⟩ := P.nonempty_boundary_homeomorph_circle hP hinj
    let x : P.boundary ℝ := ⟨q, hq⟩
    have hc := (Circle.isConnected_compl_singleton (e x)).image e.symm
      e.symm.continuous.continuousOn
    rw [e.symm.image_compl, image_singleton, e.symm_apply_apply] at hc
    have h := hc.image ((↑) : P.boundary ℝ → ℝ × ℝ) continuous_subtype_val.continuousOn
    rw [image_compl_eq_range_sdiff_image Subtype.val_injective,
      Subtype.range_coe, image_singleton] at h
    exact h
  · rw [sdiff_singleton_eq_self hq]
    exact P.isConnected_boundary hP hinj

/-- Deleting one point from a simple polygon boundary does
not change its ambient closure. See Alexander p. 7 and the
relative-density argument in M76 derivation 151. -/
theorem closure_boundary_sdiff_singleton (q : ℝ × ℝ) :
    closure (P.boundary ℝ \ {q}) = P.boundary ℝ := by
  classical
  by_cases hq : q ∈ P.boundary ℝ
  · obtain ⟨e⟩ := P.nonempty_boundary_homeomorph_circle hP hinj
    let : ConnectedSpace (P.boundary ℝ) := e.connectedSpace_iff.mpr inferInstance
    let : Nontrivial Circle := ⟨⟨Circle.exp Real.pi, 1, Circle.exp_pi_ne_one⟩⟩
    let : Nontrivial (P.boundary ℝ) := e.surjective.nontrivial
    let x : P.boundary ℝ := ⟨q, hq⟩
    have hd := (dense_compl_singleton x).closure_eq
    have h := image_closure_subset_closure_image continuous_subtype_val
      (s := ({x}ᶜ : Set (P.boundary ℝ)))
    rw [hd, image_univ, Subtype.range_coe,
      image_compl_eq_range_sdiff_image Subtype.val_injective,
      Subtype.range_coe, image_singleton] at h
    exact (closure_minimal sdiff_subset P.isClosed_boundary).antisymm h
  · rw [sdiff_singleton_eq_self hq, P.isClosed_boundary.closure_eq]

end Polygon
