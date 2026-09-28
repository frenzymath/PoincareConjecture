import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Filled
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.RegionSide



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def transverseCoordinates : (Real × Real) ≃ₜ E2 where
  toFun z := (-z.2) • EuclideanSpace.single 0 1 + z.1 • EuclideanSpace.single 1 1
  invFun p := (p 1, -p 0)
  left_inv z := by simp
  right_inv p := by ext i; fin_cases i <;> simp
  continuous_toFun := (continuous_snd.neg.smul continuous_const).add
    (continuous_fst.smul continuous_const)
  continuous_invFun := (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).continuous.prodMk
    (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).continuous.neg



theorem eventually_filled_disk_iff_wall_nonpos
    (A D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hbound : ∀ x ∈ A '' sphere (0 : E2) 1, D x 0 ≤ 0)
    {p : E2} (hp : D p 0 = 0)
    (hfront : ∀ᶠ x in 𝓝 p, x ∈ A '' sphere (0 : E2) 1 ↔ D x 0 = 0) :
    ∀ᶠ x in 𝓝 p,
      (x ∈ A '' closedBall (0 : E2) 1 ↔ D x 0 ≤ 0) ∧
      (x ∈ interior (A '' closedBall (0 : E2) 1) ↔ D x 0 < 0) := by
  let C := A '' closedBall (0 : E2) 1
  let L : E2 →L[Real] Real := EuclideanSpace.proj 0
  have hLs : Surjective L := by
    intro t
    exact ⟨EuclideanSpace.single 0 t, by simp [L]⟩
  have hopen : IsOpenMap (fun x : E2 => D x 0) :=
    (L.isOpenMap hLs).comp D.toHomeomorph.isOpenMap
  have hC : IsClosed C := ((isCompact_closedBall (0 : E2) 1).image A.continuous).isClosed
  have hboundary : frontier C = A '' sphere (0 : E2) 1 := by
    have h := A.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    rw [frontier_closedBall 0 one_ne_zero] at h
    exact h.symm
  have hregular : closure (interior C) = C := by
    change closure (interior (A.toHomeomorph '' closedBall (0 : E2) 1)) = _
    rw [← A.toHomeomorph.image_interior,
      interior_closedBall (0 : E2) one_ne_zero, ← A.toHomeomorph.image_closure,
      closure_ball (0 : E2) one_ne_zero]
    rfl
  have hinside : ∀ x ∈ interior C, D x 0 < 0 :=
    Side.coordinate_strict_bound_on_interior _ hopen
      (Side.filled_disk_coordinate_bound A D 0 hbound)
  let e := (transverseCoordinates.trans D.toHomeomorph.symm).toOpenPartialHomeomorph
  have he : e ((D p) 1, 0) = p := by
    change D.symm (transverseCoordinates ((D p) 1, 0)) = p
    have hc : transverseCoordinates ((D p) 1, 0) = D p := by
      ext i
      fin_cases i <;> simp [transverseCoordinates, hp]
    rw [hc, D.symm_apply_apply]
  have htime : ∀ z : Real × Real, D (e z) 0 = -z.2 := by
    intro z
    change D (D.symm (transverseCoordinates z)) 0 = _
    rw [D.apply_symm_apply]
    simp [transverseCoordinates]
  have hpC : p ∈ C := image_mono sphere_subset_closedBall ((hfront.self_of_nhds).mpr hp)
  have hacc : e ((D p) 1, 0) ∈ closure (interior C) := by
    rw [he, hregular]
    exact hpC
  have hf : ∀ᶠ x in 𝓝 (e ((D p) 1, 0)), x ∈ frontier C ↔ D x 0 = 0 := by
    rw [he, hboundary]
    exact hfront
  have h := Poincare.Topology.eventually_region_iff_of_transverse_coordinates e
    (show ((D p) 1, (0 : Real)) ∈ e.source from mem_univ _) hC
    (Eventually.of_forall htime) hf (Eventually.of_forall hinside) hacc
  rwa [he] at h



theorem exists_common_filled_side_neighborhood
    (A B D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : ∀ x ∈ A '' sphere (0 : E2) 1, D x 0 ≤ 0)
    (hB : ∀ x ∈ B '' sphere (0 : E2) 1, D x 0 ≤ 0)
    {K : Set E2} (hK : ∀ p ∈ K, D p 0 = 0)
    (hfrontA : ∀ p ∈ K, ∀ᶠ x in 𝓝 p,
      x ∈ A '' sphere (0 : E2) 1 ↔ D x 0 = 0)
    (hfrontB : ∀ p ∈ K, ∀ᶠ x in 𝓝 p,
      x ∈ B '' sphere (0 : E2) 1 ↔ D x 0 = 0) :
    ∃ V : Set E2, IsOpen V ∧ K ⊆ V ∧
      V ∩ (A '' closedBall (0 : E2) 1) = V ∩ (B '' closedBall (0 : E2) 1) := by
  let S := {x : E2 | x ∈ A '' closedBall (0 : E2) 1 ↔ x ∈ B '' closedBall (0 : E2) 1}
  refine ⟨interior S, isOpen_interior, ?_, ?_⟩
  · intro p hp
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [eventually_filled_disk_iff_wall_nonpos A D hA (hK p hp) (hfrontA p hp),
      eventually_filled_disk_iff_wall_nonpos B D hB (hK p hp) (hfrontB p hp)] with x hxA hxB
    exact hxA.1.trans hxB.1.symm
  · ext x
    constructor
    · rintro ⟨hx, hxA⟩
      exact ⟨hx, (interior_subset hx).mp hxA⟩
    · rintro ⟨hx, hxB⟩
      exact ⟨hx, (interior_subset hx).mpr hxB⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching
