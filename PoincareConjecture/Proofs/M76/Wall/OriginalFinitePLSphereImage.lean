import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_chartwisePLSphere_image
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) {g : E → X}
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {T : Set E} (hTK : T ⊆ K.space)
    (b : T ≃ₜ sphere (0 : V3) 1) (hb : b.IsFinitePL) :
    Nonempty (ChartwisePLSphere e (g '' T)) := by
  classical
  have hbcopy := hb
  obtain ⟨_, ⟨J, hJ, hJT, _⟩, _⟩ := hbcopy
  have hT : IsCompact T := by
    rw [← hJT]
    exact J.isCompact_space_of_finite hJ
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let q₀ : T ≃ g '' T := Equiv.Set.imageOfInjOn g T (hgi.mono hTK)
  have hq₀ : Continuous q₀ :=
    (hg.continuousOn.mono hTK).domRestrict.subtype_mk _
  let q : T ≃ₜ g '' T := q₀.toHomeomorphOfContinuousClosed hq₀ hq₀.isClosedMap
  obtain ⟨v, hv, hveq⟩ := hb.symm
  have hvK : MapsTo v (sphere (0 : V3) 1) K.space := by
    intro x hx
    rw [← hveq ⟨x, hx⟩]
    exact hTK (b.symm ⟨x, hx⟩).property
  have hPL : PolyhedralPLInCharts e (g ∘ v) (sphere (0 : V3) 1) := by
    have hvcopy := hv
    obtain ⟨N, hN, hNs, _⟩ := hvcopy
    rw [← hNs]
    exact hg.comp_finitePiecewiseAffineOn N hN (hNs.symm ▸ hv)
      (by simpa only [hNs] using hvK)
  refine ⟨{
    parametrization := b.symm.trans q
    map := g ∘ v
    map_eq := ?_
    piecewiseAffine := hPL
  }⟩
  intro x
  change g (v x) = g (b.symm x)
  exact congrArg g (hveq x).symm

end PoincareConjecture.M76
