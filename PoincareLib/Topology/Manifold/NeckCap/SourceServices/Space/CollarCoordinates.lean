import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Topology3D.Geometry.Services
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.CollarChart

/-!
# Coordinates for the specified sphere collar

The smoothness, injectivity, and immersion hypotheses in the fixed
IsCollarEmbedding interface supply a smooth open chart and a defining
function. This specializes the local-surface construction used in
Hatcher, Notes on Basic 3-Manifold Topology, Theorem 1.1, pp. 1-2.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

variable (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)

include hψ

/-- The fixed collar interface has a smooth inverse on its full image.
Its source and forward map are exactly the supplied ones. -/
theorem exists_collar_chart :
    ∃ e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) E3,
      (e : UnitTwoSphere × ℝ → E3) = ψ ∧
      e.source = univ ×ˢ Ioo (-1) 1 ∧
      e.target = ψ '' (univ ×ˢ Ioo (-1) 1) ∧
      ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
  have : Nonempty UnitTwoSphere := (NormedSpace.sphere_nonempty
    (E := E3) (x := 0) |>.mpr zero_le_one).coe_sort
  exact exists_smooth_product_chart (E := EuclideanSpace ℝ (Fin 2))
    ψ (isOpen_univ.prod isOpen_Ioo)
    hψ.1 hψ.2.1 hψ.2.2 (by simp [Module.finrank_prod])

/-- The image of the collar is an open ambient neighborhood of its
central sphere, by the inverse function theorem. -/
theorem collar_image_open : IsOpen (ψ '' (univ ×ˢ Ioo (-1) 1)) := by
  obtain ⟨e, _, _, htarget, _⟩ := exists_collar_chart ψ hψ
  rw [← htarget]
  exact e.open_target

/-- The collar parameter is a smooth ambient defining function with
nonzero derivative everywhere on the specified collar image. -/
theorem exists_sphere_collar_defining_function :
    ∃ ρ : E3 → ℝ, ContDiffOn ℝ ∞ ρ (ψ '' (univ ×ˢ Ioo (-1) 1)) ∧
      (∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)), ρ (ψ p) = p.2) ∧
      ∀ y ∈ ψ '' (univ ×ˢ Ioo (-1) 1), fderiv ℝ ρ y ≠ 0 := by
  have : Nonempty UnitTwoSphere := (NormedSpace.sphere_nonempty
    (E := E3) (x := 0) |>.mpr zero_le_one).coe_sort
  exact exists_collar_defining_function (E := EuclideanSpace ℝ (Fin 2))
    ψ (isOpen_univ.prod isOpen_Ioo)
    hψ.1 hψ.2.1 hψ.2.2 (by simp [Module.finrank_prod])

/-- A closed parameter band strictly inside the collar has compact
image. The statement also allows an empty interval. -/
theorem collar_closedBand_compact {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    IsCompact (ψ '' (univ ×ˢ Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply hψ.1.continuousOn.mono
  intro p hp
  exact ⟨hp.1, ha.trans_le hp.2.1, hp.2.2.trans_lt hb⟩

end PoincareMT.M25.Topology3D
