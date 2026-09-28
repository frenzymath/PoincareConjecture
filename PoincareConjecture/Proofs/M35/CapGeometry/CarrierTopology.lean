import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch
import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapModelEquivalence

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

noncomputable def transported {kind : CapModelKind} {p : RealProjectiveThree}
    {U : Set M} (C : CapModelEquivalence kind p U)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hU : U ⊆ phi.source) :
    CapModelEquivalence kind p (phi '' U) := by
  let : TopologicalSpace C.model := C.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.model := C.model_charted
  have : IsManifold (𝓡 3) ∞ C.model := C.model_manifold
  have himage : phi '' U ⊆ phi.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact phi.map_source (hU hx)
  have hinverse : MapsTo phi.invFun (phi '' U) U := by
    rintro _ ⟨x, hx, rfl⟩
    have hleft : phi.invFun (phi x) = x := phi.left_inv (hU hx)
    exact hleft.symm ▸ hx
  refine {
    model := C.model
    model_topology := C.model_topology
    model_charted := C.model_charted
    model_manifold := C.model_manifold
    standard_model := C.standard_model
    standard_smooth := C.standard_smooth
    forward := C.forward ∘ phi.invFun
    inverse := phi ∘ C.inverse
    inverse_mem := fun y => ⟨C.inverse y, C.inverse_mem y, rfl⟩
    left_inverse := ?_
    right_inverse := ?_
    forward_smooth := C.forward_smooth.comp
      (phi.contMDiffOn_invFun.mono himage) hinverse
    inverse_smooth := phi.contMDiffOn_toFun.comp C.inverse_smooth
      (fun y _ => hU (C.inverse_mem y))
  }
  · rintro _ ⟨x, hx, rfl⟩
    change phi (C.inverse (C.forward (phi.invFun (phi x)))) = phi x
    have hleft : phi.invFun (phi x) = x := phi.left_inv (hU hx)
    rw [hleft, C.left_inverse x hx]
  · intro y
    change C.forward (phi.invFun (phi (C.inverse y))) = y
    have hleft : phi.invFun (phi (C.inverse y)) = C.inverse y :=
      phi.left_inv (hU (C.inverse_mem y))
    rw [hleft, C.right_inverse y]

end PoincareConjecture.CapModelEquivalence

namespace PoincareConjecture.CapCertificate

private theorem actual_image_relation {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {S : Set X}
    (hS : S ⊆ e.source) : e.IsImage S (e '' S) := by
  intro x hx
  constructor
  · rintro ⟨z, hz, heq⟩
    exact e.injOn (hS hz) hx heq ▸ hz
  · intro hs
    exact mem_image_of_mem e hs

private theorem image_interior {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {S : Set X}
    (hS : S ⊆ e.source) : e '' interior S = interior (e '' S) := by
  have htarget : e '' S ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hS hx)
  have h := (actual_image_relation e hS).interior.image_eq
  rwa [inter_eq_right.mpr (interior_subset.trans hS),
    inter_eq_right.mpr (interior_subset.trans htarget)] at h

private theorem image_frontier_compact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {S : Set X}
    (hS : S ⊆ e.source) (hcompact : IsCompact S) :
    e '' frontier S = frontier (e '' S) := by
  have htarget : e '' S ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hS hx)
  have himagecompact := hcompact.image_of_continuousOn (e.continuousOn.mono hS)
  have hs : frontier S ⊆ S := hcompact.isClosed.frontier_subset
  have ht : frontier (e '' S) ⊆ e '' S := himagecompact.isClosed.frontier_subset
  have h := (actual_image_relation e hS).frontier.image_eq
  rwa [inter_eq_right.mpr (hs.trans hS), inter_eq_right.mpr (ht.trans htarget)] at h

theorem transported_core_topology
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [T2Space N]
    {g : RiemannianMetric 3 M} (C : CapCertificate g)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hU : C.carrier ⊆ phi.source) :
    IsOpen (phi '' C.carrier) ∧ IsCompact (phi '' C.closed_core) ∧
      phi '' C.core = interior (phi '' C.closed_core) ∧
      phi '' C.boundary_sphere = frontier (phi '' C.closed_core) ∧
      phi '' C.closed_core = phi '' C.carrier \ phi '' C.end_neck.carrier := by
  have hcore : C.closed_core ⊆ C.carrier := by
    rw [C.closed_core_eq_complement_end]
    exact sdiff_subset
  refine ⟨phi.toOpenPartialHomeomorph.isOpen_image_of_subset_source C.carrier_open hU,
    C.closed_core_compact.image_of_continuousOn
      (phi.contMDiffOn_toFun.continuousOn.mono (hcore.trans hU)), ?_, ?_, ?_⟩
  · rw [C.core_eq_interior_closed_core]
    exact image_interior phi.toOpenPartialHomeomorph (hcore.trans hU)
  · rw [← C.core_frontier_eq_boundary]
    exact image_frontier_compact phi.toOpenPartialHomeomorph
      (hcore.trans hU) C.closed_core_compact
  · rw [C.closed_core_eq_complement_end]
    exact (phi.toPartialEquiv.injOn.mono hU).image_sdiff_subset C.end_neck_subset

end PoincareConjecture.CapCertificate
