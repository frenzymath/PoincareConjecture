import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RetainedAtlasDomains
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs

set_option autoImplicit false
open Set Metric Geometry

namespace Geometry

theorem PolyhedralPLInCharts.of_retained_charts
    {E X V ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V} {a : κ → OpenPartialHomeomorph X V}
    {f : E → X} {S : Set E} {O : Set X}
    (hf : PolyhedralPLInCharts e f S) (hO : IsOpen O) (hfO : MapsTo f S O)
    (r : ι → κ) (hret : ∀ i, a (r i) = (e i).restrOpen O hO) :
    PolyhedralPLInCharts a f S := by
  refine ⟨hf.continuousOn, ?_⟩
  intro x
  obtain ⟨i, J, W, hJ, hJS, hW, hxW, hWJ, hfJ, hPL⟩ := hf.coordinates x
  refine ⟨r i, J, W, hJ, hJS, hW, hxW, hWJ, ?_, ?_⟩
  · intro y hy
    rw [hret i]
    exact ⟨hfJ hy, hfO (hJS hy)⟩
  · rw [hret i]
    exact hPL

end Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

def ChartwisePLBall.of_retained_charts
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {a : κ → OpenPartialHomeomorph X V3}
    {D S O : Set X} (b : ChartwisePLBall e D S)
    (hO : IsOpen O) (hDO : D ⊆ O)
    (r : ι → κ) (hret : ∀ i, a (r i) = (e i).restrOpen O hO) :
    ChartwisePLBall a D S where
  boundary_subset := b.boundary_subset
  parametrization := b.parametrization
  map := b.map
  map_eq := b.map_eq
  piecewiseAffine := b.piecewiseAffine.of_retained_charts hO (by
    intro x hx
    rw [b.map_eq ⟨x, hx⟩]
    exact hDO (b.parametrization ⟨x, hx⟩).property) r hret
  boundary_eq := b.boundary_eq

def HamiltonMarkedProtectedBall.of_retained_charts
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {a : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D O : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (hO : IsOpen O) (hDO : D ⊆ O)
    (r : α → β) (hret : ∀ i, a (r i) = (e i).restrOpen O hO) :
    HamiltonMarkedProtectedBall ι κ L a D where
  ball := b.ball.of_retained_charts hO hDO r hret
  subset_domain := b.subset_domain
  position := b.position

end PoincareConjecture.M76
