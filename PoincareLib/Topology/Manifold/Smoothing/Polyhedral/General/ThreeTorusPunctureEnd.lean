import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.PunctureEndNeighborhoods
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CenteredTorusCubeChart
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.StableTorusBands

/-!
# The actual simply connected puncture end of the three-torus

The literal half-period cube chart supplies compact protected
cores whose punctured complements are simply connected. The
construction uses the original topology of the period64 torus
and does not assert that those cores have PL boundary.
See Hamilton1976 p.66 and M76 derivation270.
-/

set_option autoImplicit false

open Set

namespace StableTorus

/-- Every compact protected subset avoiding the actual
three-torus puncture lies in the interior of a compact core
with simply connected punctured complement. This constructs
the topological end hypothesis used by Hamilton; it is not
the subsequent PL end-cutting theorem. See derivation270. -/
theorem exists_compact_threeTorus_puncture_core :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    ∀ A : Set ((Circle × Circle) × Circle), IsCompact A → q ∉ A →
      ∃ K : Set ((Circle × Circle) × Circle), IsCompact K ∧ A ⊆ interior K ∧ q ∉ K ∧
        IsSimplyConnected (Kᶜ \ {q}) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  dsimp only
  intro A hA hqA
  let Q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ))
  have h0 : (0 : CubeShell.Ambient) ∈ Q.source := by
    rw [AddCircle.centeredCubeQuotient_source]
    norm_num
  exact Q.exists_compact_core_simplyConnected_punctured_complement
    (by norm_num [CubeShell.Ambient, Module.finrank_prod]) h0 hA hqA

end StableTorus
