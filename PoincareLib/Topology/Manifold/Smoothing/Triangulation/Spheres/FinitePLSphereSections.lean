import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Spheres.FinitePLSphereIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.ConnectedLinkSectionNonisolation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlignedSectionNonisolation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ZeroChargeRegularPresentation

/-!
# Nonisolated and regular sections of actual finite PL spheres

The actual sphere model supplies a height-aligned complex and
connected vertex links. Both strict signs exclude isolated
zero vertices, and the zero-face hulls handle all other points.
At zero charge the complete section is therefore a disjoint
polygon union. See Alexander 1924, pp. 6--8 and M76 derivation 269.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Both height signs at every section point of an actual
finite PL convex-frontier sphere force nonisolation of its
entire zero section. No charge or genericity input is needed.
See Alexander pp. 6--8 and M76 derivation 269. -/
theorem IsFinitePL.mem_closure_zero_section_sdiff_of_both_signs
    {s : Set E} {D : Set F} {e : s ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) (A : E →ᵃ[ℝ] ℝ)
    (hsigns : ∀ x ∈ s, A x = 0 →
      x ∈ closure (s ∩ {y | 0 < A y}) ∧
        x ∈ closure (s ∩ {y | A y < 0})) :
    ∀ x ∈ s ∩ {y | A y = 0}, x ∈ closure ((s ∩ {y | A y = 0}) \ {x}) := by
  classical
  obtain ⟨K, hK, hKs, halign, _, _, hconn⟩ :=
    he.exists_height_aligned_surface_complex hD hcv hne hdim A
  have hacc : ∀ p ∈ K.vertices, A p = 0 →
      p ∈ closure ((K.space ∩ {y | A y = 0}) \ {p}) := by
    intro p hp hpA
    obtain ⟨hpos, hneg⟩ := hsigns p (hKs.subset (K.vertices_subset_space hp)) hpA
    have h := K.mem_closure_punctured_level_of_both_signs hK hp A (hconn p hp)
      (by simpa only [hKs, hpA] using hpos)
      (by simpa only [hKs, hpA] using hneg)
    simpa only [hpA] using h
  intro x hx
  have hxK : x ∈ K.space ∩ {y | A y = 0} := ⟨hKs.symm.subset hx.1, hx.2⟩
  simpa only [hKs] using halign.mem_closure_zero_section_sdiff_singleton hacc hxK

/-- A complete zero-charge section of an actual finite PL
sphere is a disjoint polygon union when both strict height
approaches hold at every section point. The optional residue
is eliminated by the proved section nonisolation.
See Alexander pp. 6--8 and M76 derivation 269. -/
theorem IsFinitePL.hasDisjointPolygonPresentation_of_zero_charge_signs
    {s : Set E} {D : Set F} {e : s ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) (A : E →ᵃ[ℝ] ℝ)
    (hpres : HasAlexanderCurvePresentation (s ∩ {x | A x = 0}) 0)
    (hsigns : ∀ x ∈ s, A x = 0 →
      x ∈ closure (s ∩ {y | 0 < A y}) ∧
        x ∈ closure (s ∩ {y | A y < 0})) :
    HasDisjointPolygonPresentation (s ∩ {x | A x = 0}) :=
  hpres.hasDisjointPolygonPresentation_of_nonisolated
    (he.mem_closure_zero_section_sdiff_of_both_signs hD hcv hne hdim A hsigns)

end Homeomorph
