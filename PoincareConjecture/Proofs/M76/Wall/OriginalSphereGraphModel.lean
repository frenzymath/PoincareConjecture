import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_finitePL_graph_sphere
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (F : X → E) (hFc : Continuous F)
    (hFi : InjOn F S)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) :
    ∃ b : sphere (0 : V3) 1 ≃ₜ F '' S, b.IsFinitePL ∧
      ∀ x : sphere (0 : V3) 1, (b x : E) = F (s.map x) := by
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let m : sphere (0 : V3) 1 → E := fun x => F (s.parametrization x)
  have hmc : Continuous m :=
    hFc.comp (continuous_subtype_val.comp s.parametrization.continuous)
  have hmi : Function.Injective m := by
    intro x y hxy
    apply s.parametrization.injective
    apply Subtype.ext
    exact hFi (s.parametrization x).property (s.parametrization y).property hxy
  let q := (hmc.isClosedEmbedding hmi).isEmbedding.toHomeomorph
  have himage : range m = F '' S := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨s.parametrization x, (s.parametrization x).property, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨s.parametrization.symm ⟨y, hy⟩, ?_⟩
      change F (s.parametrization (s.parametrization.symm ⟨y, hy⟩)) = F y
      rw [s.parametrization.apply_symm_apply]
  let b := q.trans (Homeomorph.setCongr himage)
  have hb (x : sphere (0 : V3) 1) : (b x : E) = F (s.map x) := by
    change F (s.parametrization x) = F (s.map x)
    rw [s.map_eq x]
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsK : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
  have hPL : FinitePiecewiseAffineOn (F ∘ s.map) (sphere (0 : V3) 1) := by
    simpa only [hKs] using hsK.finitePiecewiseAffineOn_comp K hK hF
  exact ⟨b, ⟨F ∘ s.map, hPL, hb⟩, hb⟩

end PoincareConjecture.M76
