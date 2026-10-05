import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLIrreducibility

/-!
# Transport of original PL charts by ambient homeomorphisms

Pulling back both charts leaves their full coordinate transition
unchanged. The same finite polyhedral certificates therefore transport
the domain, spheres, and balls without changing their PL coordinates.
These are the original-atlas adapters for the lattice-coordinate step
in Hamilton 1976, Lemma 3, pp. 65--67.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A common ambient change of coordinates cancels from the full
transition map, including its exact source and target. -/
theorem homeomorph_pullback_chart_transition (h : X ≃ₜ Y)
    (e d : OpenPartialHomeomorph Y (Fin 3 → ℝ)) :
    (h.transOpenPartialHomeomorph e).symm.trans (h.transOpenPartialHomeomorph d) =
      e.symm.trans d := by
  apply OpenPartialHomeomorph.ext
  · intro z
    change d (h (h.symm (e.symm z))) = d (e.symm z)
    rw [h.apply_symm_apply]
  · intro z
    change e (h (h.symm (d.symm z))) = e (d.symm z)
    rw [h.apply_symm_apply]
  · ext z
    change (z ∈ e.target ∧ h (h.symm (e.symm z)) ∈ d.source) ↔
      (z ∈ e.target ∧ e.symm z ∈ d.source)
    rw [h.apply_symm_apply]

/-- Pulling a chart back and then forward restores that same chart,
including its complete source, target and inverse. -/
theorem homeomorph_pullback_chart_cancel (h : X ≃ₜ Y)
    (e : OpenPartialHomeomorph Y (Fin 3 → ℝ)) :
    h.symm.transOpenPartialHomeomorph (h.transOpenPartialHomeomorph e) = e := by
  apply OpenPartialHomeomorph.ext
  · intro z
    change e (h (h.symm z)) = e z
    rw [h.apply_symm_apply]
  · intro z
    change h (h.symm (e.symm z)) = e.symm z
    rw [h.apply_symm_apply]
  · ext z
    change h (h.symm z) ∈ e.source ↔ z ∈ e.source
    rw [h.apply_symm_apply]

/-- Pullback preserves all domain conditions in the actual transported
atlas, including compatible halfspace charts at the whole frontier. -/
theorem PLDomain.preimage_homeomorph {α : Type*}
    {e : α → OpenPartialHomeomorph Y (Fin 3 → ℝ)} {R : Set Y}
    (he : PLDomain e R) (h : X ≃ₜ Y) :
    PLDomain (fun i => h.transOpenPartialHomeomorph (e i)) (h ⁻¹' R) := by
  refine ⟨fun x => he.cover (h x), ?_, he.closed.preimage h.continuous, ?_⟩
  · intro i j
    rw [homeomorph_pullback_chart_transition]
    exact he.compatible i j
  · intro x hx
    have hfront : h x ∈ frontier R := by
      simpa only [← h.preimage_frontier, mem_preimage] using hx
    obtain ⟨ell, v, B, hv, hxB, hxell, hcompat, hBR⟩ := he.halfspace (h x) hfront
    refine ⟨ell, v, h.transOpenPartialHomeomorph B, hv, hxB, hxell, ?_, ?_⟩
    · intro i
      rw [homeomorph_pullback_chart_transition]
      exact hcompat i
    · intro y hy
      exact hBR (h y) hy

end PoincareMT.M76

namespace Geometry

variable {E X Y α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal finite polyhedral charts pull back through an ambient
homeomorphism; the source polyhedra and their coordinate maps are retained. -/
theorem PolyhedralPLInCharts.pullback_homeomorph
    {e : α → OpenPartialHomeomorph Y (Fin 3 → ℝ)} {f : E → Y} {S : Set E}
    (hf : PolyhedralPLInCharts e f S) (h : X ≃ₜ Y) :
    PolyhedralPLInCharts (fun i => h.transOpenPartialHomeomorph (e i))
      (h.symm ∘ f) S := by
  refine ⟨h.symm.continuous.comp_continuousOn hf.continuousOn, ?_⟩
  intro x
  obtain ⟨i, K, V, hK, hKS, hV, hxV, hVK, hfK, hPL⟩ := hf.coordinates x
  refine ⟨i, K, V, hK, hKS, hV, hxV, hVK, ?_, ?_⟩
  · intro y hy
    change h (h.symm (f y)) ∈ (e i).source
    rw [h.apply_symm_apply]
    exact hfK hy
  · apply hPL.congr
    intro y _
    change e i (f y) = e i (h (h.symm (f y)))
    rw [h.apply_symm_apply]

end Geometry

namespace PoincareMT.M76

open Metric

variable {X Y α : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {e : α → OpenPartialHomeomorph Y (Fin 3 → ℝ)}

/-- The entire marked PL sphere pulls back in the same original charts. -/
theorem ChartwisePLSphere.nonempty_preimage_homeomorph {S : Set Y}
    (hS : Nonempty (ChartwisePLSphere e S)) (h : X ≃ₜ Y) :
    Nonempty (ChartwisePLSphere (fun i => h.transOpenPartialHomeomorph (e i))
      (h ⁻¹' S)) := by
  obtain ⟨s⟩ := hS
  let q : (h ⁻¹' S) ≃ₜ S := h.subtype (fun _ => Iff.rfl)
  refine ⟨{
    parametrization := s.parametrization.trans q.symm
    map := h.symm ∘ s.map
    map_eq := ?_
    piecewiseAffine := s.piecewiseAffine.pullback_homeomorph h }⟩
  intro z
  change h.symm (s.map z) = h.symm (s.parametrization z)
  rw [s.map_eq]

/-- The same whole PL ball and its marked sphere pull back together. -/
theorem ChartwisePLBall.nonempty_preimage_homeomorph {D S : Set Y}
    (hD : Nonempty (ChartwisePLBall e D S)) (h : X ≃ₜ Y) :
    Nonempty (ChartwisePLBall (fun i => h.transOpenPartialHomeomorph (e i))
      (h ⁻¹' D) (h ⁻¹' S)) := by
  obtain ⟨b⟩ := hD
  let q : (h ⁻¹' D) ≃ₜ D := h.subtype (fun _ => Iff.rfl)
  refine ⟨{
    boundary_subset := preimage_mono b.boundary_subset
    parametrization := b.parametrization.trans q.symm
    map := h.symm ∘ b.map
    map_eq := ?_
    piecewiseAffine := b.piecewiseAffine.pullback_homeomorph h
    boundary_eq := ?_ }⟩
  · intro z
    change h.symm (b.map z) = h.symm (b.parametrization z)
    rw [b.map_eq]
  · intro z
    change h (h.symm (b.parametrization z)) ∈ S ↔ _
    rw [h.apply_symm_apply]
    exact b.boundary_eq z

/-- Irreducibility transfers with its actual sphere and ball witnesses,
without changing the original chart families by a PL compatibility axiom. -/
theorem IsPLIrreducible.preimage_homeomorph {R : Set Y}
    (hI : IsPLIrreducible e R) (h : X ≃ₜ Y) :
    IsPLIrreducible (fun i => h.transOpenPartialHomeomorph (e i)) (h ⁻¹' R) := by
  refine ⟨hI.1.preimage_homeomorph h, ?_⟩
  intro S hS hSphere
  have hSphere' : Nonempty (ChartwisePLSphere e (h.symm ⁻¹' S)) := by
    simpa only [homeomorph_pullback_chart_cancel] using
      ChartwisePLSphere.nonempty_preimage_homeomorph hSphere h.symm
  have hS' : h.symm ⁻¹' S ⊆ interior R := by
    intro y hy
    have hz := hS hy
    rw [← h.preimage_interior] at hz
    simpa only [mem_preimage, h.apply_symm_apply] using hz
  obtain ⟨D, hDR, hD⟩ := hI.2 _ hS' hSphere'
  refine ⟨h ⁻¹' D, preimage_mono hDR, ?_⟩
  have hcancel : h ⁻¹' (h.symm ⁻¹' S) = S := by
    ext x
    simp only [mem_preimage, h.symm_apply_apply]
  simpa only [hcancel] using ChartwisePLBall.nonempty_preimage_homeomorph hD h

end PoincareMT.M76
