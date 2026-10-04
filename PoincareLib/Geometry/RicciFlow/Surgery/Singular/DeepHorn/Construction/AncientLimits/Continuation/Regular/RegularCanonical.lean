import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Extension.Canonical
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Continuation.Regular.CommonRegularTime

/-!
# Original canonical control at an actual regular extended point

Morgan--Tian Claim 11.35, printed pp. 289-291. The actual preterminal
point supplies time-domain membership, and the original cutoff and
four-way certificate transport through the supplied extension.
Reviewed derivation: `claim11_35-common-regular-time.md`, section 4.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

/-- At an actual preterminal regular point, the supplied extension retains
the original canonical certificate and absolute cutoff. Source:
Claim 11.35, printed pp. 289-291, with regular-time Assumptions 11.18. -/
theorem extension_canonical_control_of_regular_preterminal
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    {t : ℝ} (htT : t < T) (hregular : t ∉ H.singularTimes)
    (x : (E.extended.slice t).carrier)
    (hscalar : H.r₀⁻¹ ^ 2 ≤ E.extended.scalar ⟨t, x⟩) :
    GeneralizedCanonicalControl t x H.epsilon H.constant := by
  have hext : t ∈ E.extended.interval :=
    (E.extended.slice_nonempty_iff t).mp ⟨x⟩
  have ht : t ∈ F.interval := by
    rcases E.times_subset hext with hold | hterminal
    · exact hold
    · exact (htT.ne (mem_singleton_iff.mp hterminal)).elim
  have hcanonical : generalizedSliceStrongCanonicalNeighborhoods F H.epsilon H.constant
      (H.r₀⁻¹ ^ 2) t := by
    intro y hy
    exact ⟨H.canonical_control t ht (Or.inr hregular) y hy⟩
  exact (extension_slice_canonical E t ht H.epsilon H.constant
    (H.r₀⁻¹ ^ 2) hcanonical x hscalar).some

end PoincareMT.M32
