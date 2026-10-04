import PoincareLib.Topology.Manifold.NeckCap.Theory
import Mathlib.Topology.Connected.Basic

/-!
# Cap core contact and the stored boundary

A preconnected set avoiding a cap's stored core boundary lies in the
core whenever its closure meets that core. The actual capped-tube
carrier therefore meets the boundary of a contacted core when its cap
truncation is not contained there. Morgan--Tian Claim A.23, pp. 511-512;
see the independently reviewed cap-core-contact plan.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

/-- Closure contact with the actual core forces containment when a
preconnected set avoids the stored boundary. MT Claim A.23, pp. 511-512. -/
theorem CapCertificate.subset_core_of_avoids_boundary
    (C : CapCertificate g) {V : Set M}
    (hV : IsPreconnected V) (havoid : Disjoint V C.boundary_sphere)
    (hmeet : (closure V ∩ C.core).Nonempty) :
    V ⊆ C.core := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hclosed : IsClosed C.closed_core := C.closed_core_compact.isClosed
  have hopen : IsOpen C.core := by
    rw [C.core_eq_interior_closed_core]
    exact isOpen_interior
  have hcover : V ⊆ interior C.closed_core ∪ C.closed_coreᶜ := by
    intro x hx
    by_cases hxclosed : x ∈ C.closed_core
    · left
      by_contra hxint
      have hxboundary : x ∈ C.boundary_sphere := by
        rw [← C.core_frontier_eq_boundary]
        exact ⟨subset_closure hxclosed, hxint⟩
      exact Set.disjoint_left.mp havoid hx hxboundary
    · exact Or.inr hxclosed
  rcases hV.subset_or_subset isOpen_interior hclosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · rw [C.core_eq_interior_closed_core]
    exact hin
  · have hcomp : V ⊆ C.coreᶜ := by
      intro x hx hxcore
      rw [C.core_eq_interior_closed_core] at hxcore
      exact hout hx (interior_subset hxcore)
    have hclosure : closure V ⊆ C.coreᶜ := closure_minimal hcomp hopen.isClosed_compl
    obtain ⟨x, hxclosure, hxcore⟩ := hmeet
    exact (hclosure hxclosure hxcore).elim

/-- A contacted core has an actual boundary point in a capped tube whose
cap truncation is not inside that core. MT Claim A.23, pp. 511-512. -/
theorem CappedTubeCertificate.exists_boundary_point_of_core_contact
    (K : CappedTubeCertificate g) (C : CapCertificate g)
    (hmeet : (closure K.carrier ∩ C.core).Nonempty)
    (hno : ¬ (K.cap.carrier \
      K.cap.end_neck.region (K.cap.epsilon⁻¹ / 2) K.cap.epsilon⁻¹ ⊆ C.core)) :
    (K.carrier ∩ C.boundary_sphere).Nonempty := by
  classical
  by_contra hnone
  have havoid : Disjoint K.carrier C.boundary_sphere := by
    rw [Set.disjoint_left]
    intro x hxK hxboundary
    exact hnone ⟨x, hxK, hxboundary⟩
  have hsub := C.subset_core_of_avoids_boundary K.connected.isPreconnected havoid hmeet
  exact hno (fun _ hx => hsub (K.cap_subset hx.1))

end PoincareMT
