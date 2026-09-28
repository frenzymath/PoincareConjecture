import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallBoundaryCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => closedBall (0 : V3) 1
local notation "Q3" => sphere (0 : V3) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {C S : Set X} {M B : Set E}




theorem ChartwisePLBall.exists_prescribed_boundary_extension
    (b : ChartwisePLBall e C S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hM : IsFinitePLBallPair E M B)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKB : K.space = B)
    (Hb : B ≃ₜ S) (f : E → X) (hf : PolyhedralPLInCharts e f B)
    (hHbval : ∀ z : B, (Hb z : X) = f z) :
    ∃ (H : M ≃ₜ C) (u : E → X), PolyhedralPLInCharts e u M ∧
      (∀ z : M, u z = (H z : X)) ∧ EqOn u f B ∧
      ∀ z : M, u z ∈ S ↔ (z : E) ∈ B := by
  obtain ⟨qH, hqH, hqval⟩ :=
    b.exists_finitePL_boundary_parameter hcompat K hK hKB Hb f hf hHbval
  have hC3 : IsFinitePLBallPair V3 C3 Q3 := isFinitePLBallPair_unit_cube
  obtain ⟨A, hA, hAb, hAmem⟩ := hM.exists_extension hC3 qH hqH
  obtain ⟨v, hv, hvval⟩ := hA
  have hvmap : MapsTo v M C3 := by
    intro x hx
    rw [← hvval ⟨x, hx⟩]
    exact (A ⟨x, hx⟩).property
  let H : M ≃ₜ C := A.trans b.parametrization
  let u : E → X := b.map ∘ v
  have hvalue (z : M) : u z = (H z : X) := by
    change b.map (v z) = (b.parametrization (A z) : X)
    rw [← hvval z, b.map_eq]
  have hvCopy := hv
  obtain ⟨J, hJ, hJM, _⟩ := hvCopy
  have hu : PolyhedralPLInCharts e u M := by
    have h := b.piecewiseAffine.comp_finitePiecewiseAffineOn J hJ
      (hJM.symm ▸ hv) (fun _ hz => hvmap (hJM.subset hz))
    exact hJM ▸ h
  refine ⟨H, u, hu, hvalue, ?_, ?_⟩
  · intro x hx
    rw [hvalue ⟨x, hM.1 hx⟩]
    change (b.parametrization (A ⟨x, hM.1 hx⟩) : X) = f x
    rw [hAb ⟨x, hx⟩]
    exact (b.map_eq ⟨qH ⟨x, hx⟩, hC3.1 (qH ⟨x, hx⟩).property⟩).symm.trans
      (hqval ⟨x, hx⟩)
  · intro z
    rw [hvalue]
    exact (b.boundary_eq (A z)).trans (hAmem z).symm

end PoincareConjecture.M76
