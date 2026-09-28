import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Correction.CapBelt
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Representation








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1



theorem mem_transported_cap_iff_of_projection_mem_circle
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (g : E2 → E3)
    (hcore : g '' closedBall (0 : E2) 1 =
      Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A ''
        boundedCylinderNorthernCap v)
    (y : E3)
    (hy : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1) :
    y ∈ g '' closedBall (0 : E2) 1 ↔
      (inner Real v y - c) / s ∈ Icc (0 : Real) 1 := by
  let T := Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A
  obtain ⟨z, rfl⟩ := T.surjective y
  have hheight : (inner Real v (T z) - c) / s = inner Real v z := by
    rw [Poincare.Geometry.Euclidean.inner_liftPlaneDiffeomorph]
    field_simp
    ring
  have hAi : Injective (A : Hemisphere.Plane v → Hemisphere.Plane v) := A.injective
  have hnorm : ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖ = 1 := by
    change (Hemisphere.Plane v).orthogonalProjectionOnto (T z) ∈ A '' sphere 0 1 at hy
    rwa [Poincare.Geometry.Euclidean.projection_liftPlaneDiffeomorph,
      hAi.mem_set_image, mem_sphere_zero_iff_norm] at hy
  rw [hcore]
  change T z ∈ T '' boundedCylinderNorthernCap v ↔
    (inner Real v (T z) - c) / s ∈ Icc (0 : Real) 1
  have hTi : Injective (T : E3 → E3) := T.injective
  rw [hTi.mem_set_image, hheight]
  exact mem_boundedCylinderNorthernCap_iff_boundary_height hv hnorm

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

private theorem prepared_tube_projection_mem_circle (q : S1) {t : Real}
    (ht : t ∈ Ioo (-S.ε) S.ε) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (S.D (f (S.T (q, t)))) ∈
      S.A '' sphere 0 1 := by
  rw [S.cylinder q t ht, S.circle_image]
  simp [Hemisphere.Plane,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]



theorem prepared_tube_mem_capMinus_iff (q : S1) {t : Real}
    (ht : t ∈ Ioo (-S.ε) S.ε) :
    S.D (f (S.T (q, t))) ∈ S.gMinus '' closedBall (0 : E2) 1 ↔
      t ∈ Icc (-S.a) (-S.a + S.s) := by
  rw [mem_transported_cap_iff_of_projection_mem_circle S.unit_v (c - S.a) S.s
    S.s_pos.ne' S.A S.gMinus S.gMinus_range _
      (S.prepared_tube_projection_mem_circle q ht),
    S.height_preserving, S.tube_height q t ht]
  constructor
  · intro h
    have hlow := (le_div_iff₀ S.s_pos).mp h.1
    have hhigh := (div_le_iff₀ S.s_pos).mp h.2
    constructor <;> linarith
  · intro h
    exact ⟨(le_div_iff₀ S.s_pos).mpr (by linarith [h.1]),
      (div_le_iff₀ S.s_pos).mpr (by linarith [h.2])⟩


theorem prepared_tube_mem_capPlus_iff (q : S1) {t : Real}
    (ht : t ∈ Ioo (-S.ε) S.ε) :
    S.D (f (S.T (q, t))) ∈ S.gPlus '' closedBall (0 : E2) 1 ↔
      t ∈ Icc (S.a - S.s) S.a := by
  rw [mem_transported_cap_iff_of_projection_mem_circle S.unit_v (c + S.a) (-S.s)
    (neg_ne_zero.mpr S.s_pos.ne') S.A S.gPlus S.gPlus_range _
      (S.prepared_tube_projection_mem_circle q ht),
    S.height_preserving, S.tube_height q t ht]
  rw [show (c + t - (c + S.a)) / (-S.s) = (S.a - t) / S.s by ring]
  constructor
  · intro h
    have hlow := (le_div_iff₀ S.s_pos).mp h.1
    have hhigh := (div_le_iff₀ S.s_pos).mp h.2
    constructor <;> linarith
  · intro h
    exact ⟨(le_div_iff₀ S.s_pos).mpr (by linarith [h.2]),
      (div_le_iff₀ S.s_pos).mpr (by linarith [h.1])⟩

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
