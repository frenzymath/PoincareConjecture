import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.Pullback
import PoincareConjecture.Proofs.M76.Rigidity.OriginalMarkedProductConstruction

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem cylinderBandInterior_eq_open_parameter_image
    {X : Type*} [TopologicalSpace X] {B : Set X}
    (c : (Q ×ˢ I) ≃ₜ B) (q : V2 × ℝ → X)
    (hcq : ∀ z : Q ×ˢ I, (c z : X) = q z) :
    cylinderBandInterior c = q '' (Q ×ˢ Ioo (-1 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, ⟨z.property.1, hz⟩, (hcq z).symm.trans hzx⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, hz.2.1.le, hz.2.2.le⟩, hz.2, hcq _⟩

theorem exists_original_cylindrical_band_marked_product
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {N B : Set X}
    (he : PLDomain e N) (hN : IsCompact N)
    (c : (Q ×ˢ I) ≃ₜ B) (hB : B ⊆ frontier N)
    (q : V2 × ℝ → X) (hq : PolyhedralPLInCharts e q (Q ×ˢ I))
    (hcq : ∀ z : Q ×ˢ I, (c z : X) = q z)
    (hopen : IsOpen ((Subtype.val : frontier N → X) ⁻¹' cylinderBandInterior c))
    (j : V2 → X) (hj : PolyhedralPLInCharts e j D)
    (hji : Topology.IsEmbedding (fun z : D => j z)) (hjN : MapsTo j D N)
    (hproper : ∀ z : D, j z ∈ frontier N ↔ (z : V2) ∈ Q)
    (hrim : ∀ z : Q, j z = (c ⟨((z : V2), 0), z.property, by norm_num⟩ : X)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ P : OriginalDiskProduct e N j,
      (∀ z ∈ Q, ∀ t ∈ I, P.map (z, t) = q (z, a * t)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : N → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier N → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-v) v))) := by
  have hqi : InjOn q (Q ×ˢ I) := by
    intro x hx y hy hxy
    have hcxy : c ⟨x, hx⟩ = c ⟨y, hy⟩ :=
      Subtype.ext ((hcq ⟨x, hx⟩).trans (hxy.trans (hcq ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (c.injective hcxy)
  have hqfront : MapsTo q (Q ×ˢ I) (frontier N) := by
    intro z hz
    rw [← hcq ⟨z, hz⟩]
    exact hB (c ⟨z, hz⟩).property
  have hcenter (z : V2) (hz : z ∈ Q) : q (z, 0) = j z :=
    (hcq ⟨(z, 0), hz, by norm_num⟩).symm.trans (hrim ⟨z, hz⟩).symm
  have hopenq : IsOpen ((Subtype.val : frontier N → X) ⁻¹'
      (q '' (Q ×ˢ Ioo (-1 : ℝ) 1))) := by
    rw [← cylinderBandInterior_eq_open_parameter_image c q hcq]
    exact hopen
  obtain ⟨a, ha, hasmall, P, _, hlat, hPo⟩ :=
    exists_small_original_marked_disk_product hN he hj hji hjN hproper
      q hq hqi hqfront hcenter hopenq isOpen_univ (subset_univ _)
  exact ⟨a, ha, hasmall, P, hlat, hPo⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
