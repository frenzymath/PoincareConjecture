import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1



theorem exists_chartwise_disk_transport
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (i : ι)
    {T : Set V3} (c : D2 ≃ₜ T) (hc : c.IsFinitePL) (hT : T ⊆ (e i).target) :
    ∃ (b : D2 ≃ₜ ((e i).symm '' T)) (j : V2 → X),
      PolyhedralPLInCharts e j D2 ∧
      (∀ x : D2, j x = (b x : X)) ∧
      (∀ x : D2, (b x : X) = (e i).symm (c x)) ∧
      (∀ x : D2, e i (b x) = c x) ∧
      IsCompact ((e i).symm '' T) ∧ ((e i).symm '' T) ⊆ (e i).source := by
  obtain ⟨f, hf, hfv⟩ := hc
  let q := (e i).symm.homeomorphOfImageSubsetSource hT rfl
  let b := c.trans q
  let j := (e i).symm ∘ f
  have hmap : MapsTo f D2 (e i).target := by
    intro x hx
    rw [← hfv ⟨x, hx⟩]
    exact hT (c ⟨x, hx⟩).property
  have hcopy := hf
  obtain ⟨K, hK, hKs, _⟩ := hcopy
  have hj : PolyhedralPLInCharts e j D2 := by
    rw [← hKs]
    exact polyhedralPLInCharts_of_one_chart_inverse K hK (hKs ▸ hf) i (hKs ▸ hmap)
  refine ⟨b, j, hj, ?_, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · intro x
    change (e i).symm (f x) = (e i).symm (c x)
    rw [hfv]
  · intro x
    exact (e i).right_inv (hT (c x).property)
  · let : CompactSpace ((e i).symm '' T) := b.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  · rintro x ⟨y, hy, rfl⟩
    exact (e i).map_target (hT hy)

end PoincareConjecture.M76.Dehn
