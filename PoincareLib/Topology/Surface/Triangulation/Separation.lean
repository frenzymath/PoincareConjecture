/-
Copyright (c) 2026 The PoincareLib contributors.
-/
import PoincareLib.Topology.Plane.Jordan.Domains
import PoincareLib.Topology.Surface.Triangulation.Basic

/-!
# Separation by embedded arcs and curves in surface charts

An embedded compact arc does not separate the coordinate plane. An embedded
circle contained in a surface chart has exactly two complementary coordinate
components. These statements transfer the planar Jordan theorem to the
boundary curves used in surface subdivision.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareMT.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- A compact embedded arc contained in a chart does not separate its coordinate
plane. -/
theorem isConnected_compl_chart_unitInterval_image (p : M) {f : ℝ → M}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Icc (0 : ℝ) 1))
    (hsource : f '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    IsConnected ((chartAt (EuclideanSpace ℝ (Fin 2)) p) ''
      (f '' Icc (0 : ℝ) 1))ᶜ := by
  rw [image_image]
  apply Poincare.Topology.Plane.Jordan.isConnected_compl_image_Icc
  · exact (chartAt (EuclideanSpace ℝ (Fin 2)) p).continuousOn.comp hf
      (fun t ht => hsource ⟨t, ht, rfl⟩)
  · intro s hs t ht h
    exact hinj hs ht ((chartAt (EuclideanSpace ℝ (Fin 2)) p).injOn
      (hsource ⟨s, hs, rfl⟩) (hsource ⟨t, ht, rfl⟩) h)

/-- The coordinate complement of an embedded smooth edge is connected. -/
theorem SmoothEdge.isConnected_compl_chart_image [IsManifold (𝓡 2) ∞ M]
    (e : SmoothEdge M) (p : M) (hinj : InjOn e.map (Icc (0 : ℝ) 1))
    (hsource : e.map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    IsConnected ((chartAt (EuclideanSpace ℝ (Fin 2)) p) ''
      (e.map '' Icc (0 : ℝ) 1))ᶜ :=
  isConnected_compl_chart_unitInterval_image p e.smooth.continuousOn hinj hsource

/-- An embedded continuous circle contained in a chart has exactly two
complementary components in the coordinate plane. -/
theorem nat_card_connectedComponents_compl_chart_circle (p : M)
    {γ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → M}
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (hsource : range γ ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    Nat.card (ConnectedComponents
      (((chartAt (EuclideanSpace ℝ (Fin 2)) p) '' range γ)ᶜ :
        Set (EuclideanSpace ℝ (Fin 2)))) = 2 := by
  rw [← range_comp]
  apply Poincare.Topology.Plane.Jordan.jordan_curve
  · exact (chartAt (EuclideanSpace ℝ (Fin 2)) p).continuousOn.comp_continuous hγ
      (fun t => hsource ⟨t, rfl⟩)
  · intro s t h
    exact hinj ((chartAt (EuclideanSpace ℝ (Fin 2)) p).injOn
      (hsource ⟨s, rfl⟩) (hsource ⟨t, rfl⟩) h)

end PoincareMT.Topology.Surface
