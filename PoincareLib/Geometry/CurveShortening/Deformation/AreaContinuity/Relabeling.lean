import PoincareLib.Geometry.Riemannian.LoopSpace.Width

/-!
# Actual disk witnesses under boundary relabeling

The constant-speed relabelings in Morgan--Tian Claim 19.28, pp. 459-460,
preserve filling area as used on p. 461. M65 derivation 25 retains the
same disk map and every admissibility field, changing only the boundary
homeomorphism. No equality of the stored loop extensions is asserted.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {gamma eta : C1FreeLoopSpace (M := M)}

/-- A genuine boundary homeomorphism transports the same admissible disk
to the relabeled loop; Claim 19.28, pp. 459-460. -/
def m65RelabelSpanningDisk (e : LoopCircle ≃ₜ LoopCircle)
    (he : ∀ z, eta z = gamma (e z)) (D : LipschitzSpanningDisk g gamma) :
    LipschitzSpanningDisk g eta where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := {
    map := fun z => e.symm (D.reparameterization.map z)
    inverse := fun z => D.reparameterization.inverse (e z)
    left_inverse := fun z => by
      change D.reparameterization.inverse (e (e.symm (D.reparameterization.map z))) = z
      rw [e.apply_symm_apply, D.reparameterization.left_inverse]
    right_inverse := fun z => by
      change e.symm (D.reparameterization.map (D.reparameterization.inverse (e z))) = z
      rw [D.reparameterization.right_inverse, e.symm_apply_apply]
    continuous_map := e.symm.continuous.comp D.reparameterization.continuous_map
    continuous_inverse := D.reparameterization.continuous_inverse.comp e.continuous }
  boundary_eq z := by rw [he, e.apply_symm_apply]; exact D.boundary_eq z
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

/-- The relabeling transport preserves the actual area integral exactly;
Claim 19.28, pp. 459-460. -/
theorem m65RelabelSpanningDisk_area (e : LoopCircle ≃ₜ LoopCircle)
    (he : ∀ z, eta z = gamma (e z)) (D : LipschitzSpanningDisk g gamma) :
    (m65RelabelSpanningDisk e he D).area = D.area := rfl

/-- Relabeling preserves nonemptiness of the genuine disk class in both
directions; Claim 19.28 and the filling comparison on pp. 459-461. -/
theorem m65RelabelSpanningDisk_nonempty_iff (e : LoopCircle ≃ₜ LoopCircle)
    (he : ∀ z, eta z = gamma (e z)) :
    Nonempty (LipschitzSpanningDisk g eta) ↔ Nonempty (LipschitzSpanningDisk g gamma) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨m65RelabelSpanningDisk e.symm (fun z => by rw [he, e.apply_symm_apply]) D⟩
  · rintro ⟨D⟩
    exact ⟨m65RelabelSpanningDisk e he D⟩

/-- The complete admissible area ranges agree, not merely selected disk
areas; the filling-area use of Claim 19.28 on p. 461. -/
theorem m65RelabelSpanningDisk_areaRange (e : LoopCircle ≃ₜ LoopCircle)
    (he : ∀ z, eta z = gamma (e z)) :
    Set.range (fun D : LipschitzSpanningDisk g eta => D.area) =
      Set.range (fun D : LipschitzSpanningDisk g gamma => D.area) := by
  ext area
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨m65RelabelSpanningDisk e.symm (fun z => by rw [he, e.apply_symm_apply]) D, rfl⟩
  · rintro ⟨D, rfl⟩
    exact ⟨m65RelabelSpanningDisk e he D, rfl⟩

/-- The actual filling infimum is invariant under a boundary homeomorphism;
Claim 19.28 and its use on pp. 459-461. Genuine disk existence is retained
separately by the same-map transport. -/
theorem m65FillingArea_relabel (e : LoopCircle ≃ₜ LoopCircle)
    (he : ∀ z, eta z = gamma (e z)) : fillingArea g eta = fillingArea g gamma := by
  unfold fillingArea
  rw [m65RelabelSpanningDisk_areaRange e he]

end PoincareMT
