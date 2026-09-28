import PoincareConjecture.Proofs.M32.Claim11_32.Extension.Canonical
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.CommonRegularTime

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

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

end PoincareConjecture.M32
