import PoincareConjecture.Proofs.M76.Rigidity.OriginalMarkedProductCorrection
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSmallDiskProduct

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem exists_small_original_marked_disk_product
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z)) (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (F : E → X) (hF : PolyhedralPLInCharts e F (Q ×ˢ I))
    (hFi : InjOn F (Q ×ˢ I)) (hfront : MapsTo F (Q ×ˢ I) (frontier R))
    (hcenter : ∀ z ∈ Q, F (z, 0) = j z)
    (hopenF : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (F '' (Q ×ˢ Ioo (-1 : ℝ) 1))))
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      (∀ z ∈ Q, ∀ t ∈ I, P.map (z, t) = F (z, a * t)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-v) v))) := by
  obtain ⟨P, hPU, hPo⟩ := exists_small_original_disk_product hR he hj hemb hDR hproper hU hDU
  obtain ⟨a, ha, hasmall, P', hsub, hlat, hopen⟩ :=
    P.exists_marked_correction he (fun v hv hvsmall => (hPo v hv hvsmall).1)
      F hF hFi hfront hcenter hopenF
  refine ⟨a, ha, hasmall, P', ?_, hlat, ?_⟩
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := hsub ⟨z, hz, rfl⟩
    rw [← hwz]
    exact hPU hw
  · intro v hv hvsmall
    have ho := hopen v hv hvsmall
    exact ⟨ho, P'.isOpen_lateral_image he.closed hvsmall ho⟩

end PoincareConjecture.M76
