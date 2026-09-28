import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Rebasing.HomotopyNaturality
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeHomotopyExtension










set_option autoImplicit false

open scoped Topology unitInterval
open Topology

universe u

namespace PoincareConjecture

def m67SphereGenLoop {X : Type u} [TopologicalSpace X]
    (q : M59SphereQuotient) (F : C(LoopTwoSphere, X))
    (x : X) (hx : F q.pole = x) : GenLoop (Fin 2) X x :=
  ⟨F.comp q.map, fun z hz => by
    change F (q.map z) = x
    rw [q.boundary_collapsed z hz, hx]⟩

theorem m67_descend_cube_homotopy
    {X : Type u} [TopologicalSpace X] (q : M59SphereQuotient)
    (F : C(I × (Fin 2 → I), X))
    (hF : ∀ t z w, z ∈ Cube.boundary (Fin 2) → w ∈ Cube.boundary (Fin 2) →
      F (t, z) = F (t, w)) :
    ∃ G : C(I × LoopTwoSphere, X), ∀ t z, G (t, q.map z) = F (t, z) := by
  classical
  let lift : LoopTwoSphere → (Fin 2 → I) := fun c => (q.surjective c).choose
  have hlift (c : LoopTwoSphere) : q.map (lift c) = c := (q.surjective c).choose_spec
  let G : I × LoopTwoSphere → X := fun z => F (z.1, lift z.2)
  have hG (t : I) (z : Fin 2 → I) : G (t, q.map z) = F (t, z) := by
    change F (t, lift (q.map z)) = F (t, z)
    rcases (q.exact_fibers _ _).mp (hlift (q.map z)) with h | h
    · rw [h]
    · exact hF t _ _ h.1 h.2
  let Q : C(I × (Fin 2 → I), I × LoopTwoSphere) :=
    ⟨fun z => (z.1, q.map z.2),
      continuous_fst.prodMk (q.map.continuous.comp continuous_snd)⟩
  have hQsurj : Function.Surjective Q := by
    rintro ⟨t, c⟩
    exact ⟨(t, lift c), by change (t, q.map (lift c)) = (t, c); rw [hlift]⟩
  have hQquot : IsQuotientMap Q := Q.continuous.isClosedMap.isQuotientMap
    Q.continuous hQsurj
  have hcont : Continuous G := hQquot.continuous_iff.mpr (by
    have heq : G ∘ Q = F := by funext z; exact hG z.1 z.2
    rw [heq]
    exact F.continuous)
  exact ⟨⟨G, hcont⟩, hG⟩



theorem m67_sphere_free_transport
    (B : M59HigherBasepointTransportService.{u})
    {X : Type u} [TopologicalSpace X] (q : M59SphereQuotient)
    (F : C(LoopTwoSphere, X)) {x y : X} (hx : F q.pole = x) (p : Path x y) :
    ∃ (G : C(LoopTwoSphere, X)) (hy : G q.pole = y),
      F.Homotopic G ∧
      M59HigherBasepointTransport.map (B.transport 2) p
        (Quotient.mk' (m67SphereGenLoop q F x hx)) =
          Quotient.mk' (m67SphereGenLoop q G y hy) := by
  let side : C(I × Cube.boundary (Fin 2), X) :=
    ⟨fun z => p z.1, p.continuous.comp continuous_fst⟩
  obtain ⟨H, hH0, hHb⟩ := Poincare.Topology.exists_cube_homotopy_extension
    (F.comp q.map) side (by
      intro z
      change p 0 = F (q.map z.val)
      rw [p.source, q.boundary_collapsed z.val z.property, hx])
  obtain ⟨J, hJ⟩ := m67_descend_cube_homotopy q H (by
    intro t z w hz hw
    exact (hHb t ⟨z, hz⟩).trans (hHb t ⟨w, hw⟩).symm)
  have hJ0 (c : LoopTwoSphere) : J (0, c) = F c := by
    obtain ⟨z, rfl⟩ := q.surjective c
    rw [hJ, hH0]
    rfl
  have hJpole (t : I) : J (t, q.pole) = p t := by
    let z : Fin 2 → I := fun _ => 0
    have hz : z ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
    rw [← q.boundary_collapsed z hz, hJ]
    exact hHb t ⟨z, hz⟩
  let G : C(LoopTwoSphere, X) :=
    ⟨fun c => J (1, c), J.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hy : G q.pole = y := (hJpole 1).trans p.target
  let hom : F.Homotopy G :=
    { toContinuousMap := J
      map_zero_left := hJ0
      map_one_left := fun _ => rfl }
  refine ⟨G, hy, ⟨hom⟩, ?_⟩
  let down : C(ULift.{u} LoopTwoSphere, LoopTwoSphere) :=
    ⟨ULift.down, continuous_uliftDown⟩
  let generator : GenLoop (Fin 2) (ULift.{u} LoopTwoSphere) (ULift.up q.pole) :=
    ⟨⟨fun z => ULift.up (q.map z), continuous_uliftUp.comp q.map.continuous⟩,
      fun z hz => congrArg ULift.up (q.boundary_collapsed z hz)⟩
  exact m67_basepoint_transport_homotopy_between B (hom.compContinuousMap down)
    (ULift.up q.pole) p hx hy hJpole (Quotient.mk' generator)

theorem m67_sphere_homotopic_of_class_eq
    {X : Type u} [TopologicalSpace X] (q : M59SphereQuotient)
    (F G : C(LoopTwoSphere, X)) (x : X)
    (hF : F q.pole = x) (hG : G q.pole = x)
    (hclass : Quotient.mk' (m67SphereGenLoop q F x hF) =
      Quotient.mk' (m67SphereGenLoop q G x hG)) : F.Homotopic G := by
  obtain ⟨H⟩ := Quotient.exact hclass
  obtain ⟨J, hJ⟩ := m67_descend_cube_homotopy q H.toHomotopy.toContinuousMap (by
    intro t z w hz hw
    exact (H.prop t z hz).trans ((show F (q.map z) = F (q.map w) by
      rw [q.boundary_collapsed z hz, q.boundary_collapsed w hw]).trans
        (H.prop t w hw).symm))
  refine ⟨{ toContinuousMap := J
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro c
    obtain ⟨z, rfl⟩ := q.surjective c
    exact (hJ 0 z).trans (H.apply_zero z)
  · intro c
    obtain ⟨z, rfl⟩ := q.surjective c
    exact (hJ 1 z).trans (H.apply_one z)

end PoincareConjecture
