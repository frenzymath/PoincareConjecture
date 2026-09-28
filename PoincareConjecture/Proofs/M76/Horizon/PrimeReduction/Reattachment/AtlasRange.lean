import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility

set_option autoImplicit false
open Set Geometry

namespace Geometry

variable {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
  {a : ι → OpenPartialHomeomorph X F} {f : E → X} {S : Set E}

theorem PolyhedralPLInCharts.range (h : PolyhedralPLInCharts a f S) :
    PolyhedralPLInCharts (Subtype.val : Set.range a → OpenPartialHomeomorph X F) f S := by
  refine ⟨h.continuousOn,?_⟩
  intro x
  obtain ⟨i,K,V,hrest⟩ := h.coordinates x
  exact ⟨⟨a i,mem_range_self i⟩,K,V,hrest⟩

theorem PolyhedralPLInCharts.of_range
    (h : PolyhedralPLInCharts (Subtype.val : Set.range a → OpenPartialHomeomorph X F) f S) :
    PolyhedralPLInCharts a f S := by
  refine ⟨h.continuousOn,?_⟩
  intro x
  obtain ⟨j,K,V,hrest⟩ := h.coordinates x
  obtain ⟨i,hi⟩ := j.property
  exact ⟨i,K,V,hi.symm ▸ hrest⟩

end Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

variable {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {a : ι → OpenPartialHomeomorph X V3}
  {b : κ → OpenPartialHomeomorph Y V3} {R S D : Set X} {T : Set Y}

theorem PLDomain.range (h : PLDomain a R) :
    PLDomain (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) R := by
  refine ⟨?_,?_,h.closed,?_⟩
  · intro x
    obtain ⟨i,hi⟩ := h.cover x
    exact ⟨⟨a i,mem_range_self i⟩,hi⟩
  · rintro ⟨c,i,rfl⟩ ⟨d,j,rfl⟩
    exact h.compatible i j
  · intro x hx
    obtain ⟨ell,v,B,hv,hxB,hzero,hcompat,hhalf⟩ := h.halfspace x hx
    refine ⟨ell,v,B,hv,hxB,hzero,?_,hhalf⟩
    rintro ⟨c,i,rfl⟩
    exact hcompat i

theorem PLDomain.of_range
    (h : PLDomain (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) R) :
    PLDomain a R := by
  refine ⟨?_,?_,h.closed,?_⟩
  · intro x
    obtain ⟨⟨c,i,rfl⟩,hi⟩ := h.cover x
    exact ⟨i,hi⟩
  · intro i j
    exact h.compatible ⟨a i,mem_range_self i⟩ ⟨a j,mem_range_self j⟩
  · intro x hx
    obtain ⟨ell,v,B,hv,hxB,hzero,hcompat,hhalf⟩ := h.halfspace x hx
    exact ⟨ell,v,B,hv,hxB,hzero,fun i => hcompat ⟨a i,mem_range_self i⟩,hhalf⟩

def ChartwisePLSphere.to_range (s : ChartwisePLSphere a S) :
    ChartwisePLSphere (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) S where
  parametrization := s.parametrization
  map := s.map
  map_eq := s.map_eq
  piecewiseAffine := s.piecewiseAffine.range

def ChartwisePLSphere.of_range
    (s : ChartwisePLSphere (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) S) :
    ChartwisePLSphere a S where
  parametrization := s.parametrization
  map := s.map
  map_eq := s.map_eq
  piecewiseAffine := s.piecewiseAffine.of_range

def ChartwisePLBall.to_range (s : ChartwisePLBall a D S) :
    ChartwisePLBall (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) D S where
  boundary_subset := s.boundary_subset
  parametrization := s.parametrization
  map := s.map
  map_eq := s.map_eq
  piecewiseAffine := s.piecewiseAffine.range
  boundary_eq := s.boundary_eq

def ChartwisePLBall.of_range
    (s : ChartwisePLBall (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) D S) :
    ChartwisePLBall a D S where
  boundary_subset := s.boundary_subset
  parametrization := s.parametrization
  map := s.map
  map_eq := s.map_eq
  piecewiseAffine := s.piecewiseAffine.of_range
  boundary_eq := s.boundary_eq

theorem IsPLIrreducible.range (h : IsPLIrreducible a R) :
    IsPLIrreducible (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) R := by
  refine ⟨h.1.range,?_⟩
  rintro S hSR ⟨s⟩
  obtain ⟨D,hDR,⟨d⟩⟩ := h.2 S hSR ⟨s.of_range⟩
  exact ⟨D,hDR,⟨d.to_range⟩⟩

theorem IsPLIrreducible.of_range
    (h : IsPLIrreducible (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) R) :
    IsPLIrreducible a R := by
  refine ⟨h.1.of_range,?_⟩
  rintro S hSR ⟨s⟩
  obtain ⟨D,hDR,⟨d⟩⟩ := h.2 S hSR ⟨s.to_range⟩
  exact ⟨D,hDR,⟨d.of_range⟩⟩

theorem ChartwisePLOn.range_source {f : C(R,T)} {N : Set R}
    (h : ChartwisePLOn a b f N) :
    ChartwisePLOn (Subtype.val : Set.range a → OpenPartialHomeomorph X V3) b f N := by
  refine ⟨h.source_domain.range,h.target_domain,h.open_domain,?_⟩
  intro x hx
  obtain ⟨i,j,K,V,F,hrest⟩ := h.coordinates x hx
  exact ⟨⟨a i,mem_range_self i⟩,j,K,V,F,hrest⟩

theorem ChartwisePLOn.range_target {f : C(R,T)} {N : Set R}
    (h : ChartwisePLOn a b f N) :
    ChartwisePLOn a (Subtype.val : Set.range b → OpenPartialHomeomorph Y V3) f N := by
  refine ⟨h.source_domain,h.target_domain.range,h.open_domain,?_⟩
  intro x hx
  obtain ⟨i,j,K,V,F,hrest⟩ := h.coordinates x hx
  exact ⟨i,⟨b j,mem_range_self j⟩,K,V,F,hrest⟩

end PoincareConjecture.M76
