import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Asymptotic

/-!
# Reduced volume along the specified ancient rescaling sequence

Morgan--Tian Corollary 9.14, pp. 185-186. The constant is independent of the
positive rescaled time. This records the original flow at the dilated times;
the sequence and its reference point are exactly the frozen M18 inputs.
-/

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The same sub-Euclidean reduced-volume limit occurs at each positive time
along the specified sequence of ancient dilations. -/
theorem ancientRescalingSequence_reducedVolume_limit
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    ∃ V : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧
      ∀ τ : ℝ, 0 < τ →
        Tendsto (fun k ↦ reducedVolume K.flow 0 S.reference (S.scale k * τ))
          atTop (𝓝 V) := by
  obtain ⟨A⟩ := P.structural
  have hscalar := (A.structural M K).scalar_pos (-1 / 2) (by norm_num) S.reference
  obtain ⟨V, hV0, hVE, _, hlim⟩ :=
    exists_ancient_reducedVolume_limit_lt_euclidean K.flow P.reduced_volume
      S.reference S.reference hscalar
  exact ⟨V, hV0, hVE, hlim S.scale S.scale_tendsto⟩

end PoincareMT
