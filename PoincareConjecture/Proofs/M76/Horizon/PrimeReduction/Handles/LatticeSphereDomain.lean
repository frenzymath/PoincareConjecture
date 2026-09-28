import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeSphereBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.plDomain_of_unitBallPair
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {Q S : Set X}
    (s : ChartwisePLSphere e S) (hQ : IsCompact Q)
    (hfront : frontier Q = S) (hpair : IsUnitBallPair V3 Q S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source) : PLDomain e Q := by
  have hreg := (isConnected_interior_and_closure_of_unitBallPair hQ hfront hpair).2
  refine ⟨hcover, hcompat, hQ.isClosed, ?_⟩
  intro x hx
  exact s.exists_regular_boundary_halfspace_chart (A := ∅) hQ.isClosed hreg
    isClosed_empty hcompat hcover (by simpa only [empty_union] using hfront)
    (hfront ▸ hx) (notMem_empty x)

theorem ChartwisePLSphere.exists_lattice_ball_domains
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ Q : Set (LatticeHandleAmbient ι κ L), IsCompact Q ∧ frontier Q = S ∧
      IsUnitBallPair V3 Q S ∧ PLDomain e Q ∧ PLDomain e (interior Q)ᶜ ∧
      Q ⊆ interior (latticeHandleDomain ι κ L) := by
  obtain ⟨Q,hQ,hfront,hpair,hinside⟩ := s.exists_lattice_ball_pair L he hdim hSR
  have hdomain := s.plDomain_of_unitBallPair hQ hfront hpair he.compatible he.cover
  exact ⟨Q,hQ,hfront,hpair,hdomain,hdomain.closed_exterior,hinside⟩

end PoincareConjecture.M76
