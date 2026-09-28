import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem height_above_disk_of_cap_range {v : E3} (hv : ‖v‖ = 1)
    {f : S2 → E3} (hf : Injective f) (K : Set S2) (b : Real) {s : Real} (hs : 0 < s)
    (γ : S1 → Hemisphere.Plane v)
    (B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hboundary : ∀ q, b • v + (γ q : E3) ∈ f '' K)
    (hrange : range f = f '' K ∪
      liftPlaneDiffeomorph hv b s hs.ne' B '' boundedCylinderNorthernCap v) :
    ∀ p ∉ K, b < inner Real v (f p) := by
  intro p hp
  have hmem : f p ∈ f '' K ∪
      liftPlaneDiffeomorph hv b s hs.ne' B '' boundedCylinderNorthernCap v := by
    rw [← hrange]
    exact mem_range_self p
  rcases hmem with ⟨q, hq, he⟩ | ⟨z, hz, he⟩
  · exact (hp ((hf he) ▸ hq)).elim
  have hzh := height_nonneg_of_mem_boundedCylinderNorthernCap hz
  have hheight : inner Real v (f p) = b + s * inner Real v z := by
    rw [← he, inner_liftPlaneDiffeomorph]
  by_contra hn
  have hz0 : inner Real v z = 0 := by
    have hh := le_of_not_gt hn
    rw [hheight] at hh
    nlinarith
  have hnorm : ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖ = 1 :=
    ((mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv (by rw [hz0]; norm_num)).mp hz).2
  have hBmem : B ((Hemisphere.Plane v).orthogonalProjectionOnto z) ∈ range γ := by
    rw [← hB]
    exact ⟨_, mem_sphere_zero_iff_norm.mpr hnorm, rfl⟩
  obtain ⟨q, hq⟩ := hBmem
  have hfp : f p = b • v + (γ q : E3) := by
    rw [← he, liftPlaneDiffeomorph_apply, hz0, mul_zero, add_zero, ← hq]
  obtain ⟨x, hx, hxf⟩ := hboundary q
  have hxp : x = p := hf (hxf.trans hfp.symm)
  exact hp (hxp ▸ hx)

end Poincare.Manifold.Schoenflies
