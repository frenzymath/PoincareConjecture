import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Step
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Representation







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace Reverse

def capCoordinates {v : E3} (hv : ‖v‖ = 1)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    Diffeomorph 𝓘(Real, Hemisphere.Plane v × Real) (𝓡 3)
      (Hemisphere.Plane v × Real) E3 ∞ :=
  (((ContinuousLinearEquiv.prodComm Real (Hemisphere.Plane v) Real).trans
    (Poincare.Geometry.Euclidean.heightCoordinates hv)).toDiffeomorph).trans
      (Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv 0 1 (by norm_num) A)

@[simp] theorem capCoordinates_apply {v : E3} (hv : ‖v‖ = 1)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (p : Hemisphere.Plane v × Real) :
    capCoordinates hv A p = p.2 • v + (A p.1 : E3) := by
  change Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv 0 1 (by norm_num) A
    (p.2 • v + (p.1 : E3)) = _
  rw [Poincare.Geometry.Euclidean.liftPlaneDiffeomorph_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.1.property]

@[simp] theorem inner_capCoordinates {v : E3} (hv : ‖v‖ = 1)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (p : Hemisphere.Plane v × Real) :
    inner Real v (capCoordinates hv A p) = p.2 := by
  rw [capCoordinates_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A p.1).property]

@[simp] theorem projection_capCoordinates {v : E3} (hv : ‖v‖ = 1)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (p : Hemisphere.Plane v × Real) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (capCoordinates hv A p) = A p.1 := by
  rw [capCoordinates_apply]
  simp

theorem mem_transported_cap_iff_flat {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (q : Hemisphere.Plane v) (hq : ‖q‖ ≤ 1 / 2) (t : Real) :
    capCoordinates hv A (q, t) ∈
        Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv b s hs A ''
          boundedCylinderNorthernCap v ↔ t = b + s := by
  let x : E3 := ((t - b) / s) • v + (q : E3)
  have hproj : (Hemisphere.Plane v).orthogonalProjectionOnto x = q := by
    simp [x]
  have hheight : inner Real v x = (t - b) / s := by
    simp [x, inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.property]
  have hmap : Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv b s hs A x =
      capCoordinates hv A (q, t) := by
    rw [Poincare.Geometry.Euclidean.liftPlaneDiffeomorph_apply, hheight, hproj,
      capCoordinates_apply]
    congr 2
    field_simp
    ring
  have hmem : Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv b s hs A x ∈
      Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv b s hs A ''
        boundedCylinderNorthernCap v ↔ x ∈ boundedCylinderNorthernCap v := by
    constructor
    · rintro ⟨z, hz, he⟩
      exact (Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv b s hs A).injective he ▸ hz
    · intro hx
      exact mem_image_of_mem _ hx
  rw [← hmap, hmem,
    mem_boundedCylinderNorthernCap_iff_height hv (by rw [hproj]; linarith),
    hproj, hheight, boundedCapHeight_eq_one (by nlinarith [norm_nonneg q]), div_eq_iff hs]
  constructor <;> intro h <;> linarith

end Reverse

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem mem_capMinus_iff_flat (q : Hemisphere.Plane v) (hq : ‖q‖ ≤ 1 / 2) (t : Real) :
    Reverse.capCoordinates S.unit_v S.A (q, t) ∈ S.gMinus '' closedBall (0 : E2) 1 ↔
      t = c - S.a + S.s := by
  rw [S.gMinus_range]
  exact Reverse.mem_transported_cap_iff_flat S.unit_v _ _ S.s_pos.ne' S.A q hq t

theorem mem_capPlus_iff_flat (q : Hemisphere.Plane v) (hq : ‖q‖ ≤ 1 / 2) (t : Real) :
    Reverse.capCoordinates S.unit_v S.A (q, t) ∈ S.gPlus '' closedBall (0 : E2) 1 ↔
      t = c + S.a - S.s := by
  rw [S.gPlus_range]
  simpa only [sub_eq_add_neg, boundedCylinderNorthernCap] using
    Reverse.mem_transported_cap_iff_flat S.unit_v
    (c + S.a) (-S.s) (neg_ne_zero.mpr S.s_pos.ne') S.A q hq t

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
