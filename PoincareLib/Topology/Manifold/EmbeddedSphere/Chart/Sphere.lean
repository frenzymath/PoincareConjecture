import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.Topology.Manifold.EmbeddedSphere.Chart.Centered

/-!
# A universe-correct centered chart for the embedded sphere

The real codimension-one chart is lifted in its horizontal factor to the
ambient universe. Its exact zero-slice condition and center are unchanged.
Source: M53 derivation 11, for the separation repair of Morgan--Tian,
Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

universe u

namespace PoincareMT.Topology.EmbeddedSphere

/-- Each point of the embedded sphere admits an exact centered product
chart whose target belongs to the ambient universe. Source: the immersion
normal form and M53 derivation 11, for Morgan--Tian, p. 365. -/
theorem sphere_exists_centered_zero_slice_chart
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) (x : UnitTwoSphere) :
    ∃ e : OpenPartialHomeomorph M (ULift.{u} (EuclideanSpace ℝ (Fin 2)) × ℝ),
      S.sphere x ∈ e.source ∧ e (S.sphere x) = 0 ∧
        ∀ y ∈ e.source, y ∈ Set.range S.sphere ↔ (e y).2 = 0 := by
  obtain ⟨e, hx, he, hslice⟩ :=
    S.smooth_embedding.exists_centered_zero_slice_chart (by simp) x
  let L : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ
      (ULift.{u} (EuclideanSpace ℝ (Fin 2)) × ℝ) :=
    Homeomorph.ulift.symm.prodCongr (Homeomorph.refl ℝ)
  refine ⟨e.transHomeomorph L, hx, ?_, hslice⟩
  change L (e (S.sphere x)) = 0
  rw [he]
  rfl

end PoincareMT.Topology.EmbeddedSphere
