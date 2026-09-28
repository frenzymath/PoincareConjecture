import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedLinkSectionNonisolation
import PoincareConjecture.Proofs.M76.Mathlib.AlignedSectionNonisolation
import PoincareConjecture.Proofs.M76.Mathlib.ZeroChargeRegularPresentation

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

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
