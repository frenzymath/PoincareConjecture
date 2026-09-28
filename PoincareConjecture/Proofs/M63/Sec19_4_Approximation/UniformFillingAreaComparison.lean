import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Continuity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.SmallParametrizedCollars










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture



theorem m63_exists_uniform_filling_area_comparison
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    {Lambda epsilon : ℝ} (hLambda : 0 ≤ Lambda) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ gamma0 gamma1 : C1FreeLoopSpace (M := M),
      IsNullHomotopicLoop gamma0 → IsNullHomotopicLoop gamma1 →
      (∀ z : LoopCircle, g.edist (gamma1 z) (gamma0 z) < ENNReal.ofReal delta) →
      freeLoopLength g gamma1 + freeLoopLength g gamma0 ≤ Lambda →
      |fillingArea g gamma1 - fillingArea g gamma0| < epsilon := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact LoopAmbient M
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨delta, hdelta, hcollar⟩ :=
    m60_exists_small_parametrized_collar g hcompact hLambda hh
  refine ⟨delta, hdelta, ?_⟩
  intro gamma0 gamma1 hnull0 hnull1 hclose hlength
  obtain ⟨D0, hD0, hD0area⟩ :=
    m60FillingArea_parametrized_near_minimizer g gamma0 hnull0 (epsilon / 2) hh
  obtain ⟨D1, hD1, hD1area⟩ :=
    m60FillingArea_parametrized_near_minimizer g gamma1 hnull1 (epsilon / 2) hh
  obtain ⟨E1, _, hE1⟩ := hcollar gamma0 gamma1 hclose hlength D0 hD0
  have hreverse (z : LoopCircle) :
      g.edist (gamma0 z) (gamma1 z) < ENNReal.ofReal delta := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hsymm : g.edist (gamma0 z) (gamma1 z) = g.edist (gamma1 z) (gamma0 z) :=
      Manifold.riemannianEDist_comm
    rw [hsymm]
    exact hclose z
  obtain ⟨E0, _, hE0⟩ := hcollar gamma1 gamma0 hreverse
    (by simpa only [add_comm] using hlength) D1 hD1
  have hupper := m60FillingArea_le_disk g gamma1 E1
  have hlower := m60FillingArea_le_disk g gamma0 E0
  rw [abs_lt]
  constructor <;> linarith only [hupper, hlower, hD0area, hD1area, hE0, hE1]

end PoincareConjecture
