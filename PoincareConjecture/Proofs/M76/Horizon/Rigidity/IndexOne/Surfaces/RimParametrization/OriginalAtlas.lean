import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus



theorem exists_original_atlas_parametrization
    {E F V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    {P : Set E} {T : Set F} {S : Set X}
    (A : P ≃ₜ T) (hA : A.IsFinitePL) (Hmodel : T ≃ₜ S)
    (g : F → X) (hg : PolyhedralPLInCharts e g T)
    (hvalue : ∀ x : T, (Hmodel x : X) = g x) :
    ∃ q : E → X, PolyhedralPLInCharts e q P ∧
      ∀ x : P, ((A.trans Hmodel) x : X) = q x := by
  obtain ⟨a, ha, hAv⟩ := hA
  obtain ⟨K, hK, hKs, hfaces⟩ := ha
  have hmap : MapsTo a K.space T := by
    intro x hx
    rw [← hAv ⟨x, hKs.subset hx⟩]
    exact (A ⟨x, hKs.subset hx⟩).property
  have hcomp := hg.comp_finitePiecewiseAffineOn K hK
    ⟨K, hK, rfl, hfaces⟩ hmap
  refine ⟨g ∘ a, hKs ▸ hcomp, ?_⟩
  intro x
  exact (hvalue (A x)).trans (congrArg g (hAv x))

end PoincareConjecture.M76.HamiltonIntervalTorus
