import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Barrier
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Sequences












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}


noncomputable def overlapBarrierMap (N Q : EpsilonNeck g) :
    {x : M // x ∈ N.carrier ∩ Q.carrier} → RoundCylinderSpace :=
  fun x => ((Q.coordinate_inverse x).1, N.overlapBarrier Q x)


theorem overlapBarrierMap_continuous (N Q : EpsilonNeck g) :
    Continuous (N.overlapBarrierMap Q) := by
  have hQ : ContinuousOn (fun x => (Q.coordinate_inverse x).1)
      (N.carrier ∩ Q.carrier) :=
    Q.coordinate_inverse_smooth.continuousOn.fst.mono inter_subset_right
  exact (continuousOn_iff_continuous_domRestrict.mp hQ).prodMk
    (continuousOn_iff_continuous_domRestrict.mp (N.overlapBarrier_continuousOn Q))



theorem isProperMap_overlapBarrierMap [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] (N Q : EpsilonNeck g)
    (heq : Q.epsilon = N.epsilon)
    (hoverlap : N.carrier ∩ Q.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2))
    (hpositive : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      Q.coordinate_map '' (univ ×ˢ
        Icc (-(3 / 4 : ℝ) * N.epsilon⁻¹) ((3 / 4 : ℝ) * N.epsilon⁻¹)))
    (hnegative : Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
      N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹)) :
    IsProperMap (N.overlapBarrierMap Q) := by
  let : CompactlyCoherentSpace RoundCylinderSpace :=
    CompactlyCoherentSpace.of_sequentialSpace
  refine isProperMap_iff_isCompact_preimage.mpr
    ⟨N.overlapBarrierMap_continuous Q, fun K hK => ?_⟩
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_snd.continuousOn : ContinuousOn (Prod.snd : RoundCylinderSpace → ℝ) K)
  let A : Set {x : M // x ∈ N.carrier ∩ Q.carrier} :=
    {x | |N.overlapBarrier Q x| ≤ max B 0}
  have himage : Subtype.val '' A =
      {x | x ∈ N.carrier ∩ Q.carrier ∧ |N.overlapBarrier Q x| ≤ max B 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hbound⟩
      exact ⟨⟨x, hx⟩, hbound, rfl⟩
  have hA : IsCompact A := by
    rw [Subtype.isCompact_iff, himage]
    exact N.isCompact_overlapBarrier_band Q heq hoverlap hpositive hnegative
      (max B 0) (le_max_right _ _)
  apply hA.of_isClosed_subset (hK.isClosed.preimage (N.overlapBarrierMap_continuous Q))
  intro x hx
  exact (show |N.overlapBarrier Q x| ≤ B by
    simpa only [Real.norm_eq_abs, overlapBarrierMap] using hB (N.overlapBarrierMap Q x) hx).trans
      (le_max_left _ _)

end PoincareConjecture.EpsilonNeck
