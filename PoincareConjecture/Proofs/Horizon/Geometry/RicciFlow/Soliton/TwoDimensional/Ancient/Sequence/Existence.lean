import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Attainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Surface

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_ancientRescalingSequence_of_spatial_minimum_bound
    (K : AncientKappaSolution 2 M) (reference : M)
    (hbound : ∀ k : ℕ,
      K.spatialReducedLengthInfimum reference ((k : ℝ) + 1) ≤ 1) :
    Nonempty (AncientRescalingSequence K) := by
  let scale : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hscale_pos (k : ℕ) : 0 < scale k := by
    dsimp [scale]
    positivity
  have hscale_tendsto : Tendsto scale atTop atTop := by
    exact tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hrescale (k : ℕ) : AncientRescaling K (scale k) := by
    exact K.surfaceRescaling (scale k) (hscale_pos k)
  have hmin (k : ℕ) :
      ∃ q : M, ∀ y : M,
        reducedLength K.flow 0 reference q (scale k) ≤
          reducedLength K.flow 0 reference y (scale k) := by
    obtain ⟨q, hq⟩ := K.exists_reducedLength_minimizer reference
      (tau := scale k) (hscale_pos k)
    exact ⟨q, hq⟩
  choose base hbase using hmin
  have hbase_bound (k : ℕ) :
      reducedLength K.flow 0 reference (base k) (scale k) ≤ (2 : ℝ) / 2 := by
    obtain ⟨q, hq⟩ := K.exists_reducedLength_eq_spatialInfimum reference
      (tau := scale k) (hscale_pos k)
    have hscale : scale k = (k : ℝ) + 1 := by rfl
    have hle : reducedLength K.flow 0 reference (base k) (scale k) =
        K.spatialReducedLengthInfimum reference (scale k) := by
      apply le_antisymm
      · exact (hbase k q).trans_eq hq
      · exact K.spatialReducedLengthInfimum_le reference (base k) (scale k)
    rw [hle, hscale]
    simpa using hbound k
  exact ⟨{
    reference := reference
    scale := scale
    scale_pos := hscale_pos
    scale_tendsto := hscale_tendsto
    rescaling := hrescale
    base := base
    base_minimizing := hbase
    base_reduced_length_bound := by
      intro k
      simpa using hbase_bound k }⟩

theorem exists_ancientRescalingSequence (K : AncientKappaSolution 2 M) :
    Nonempty (AncientRescalingSequence K) := by
  classical
  obtain ⟨reference⟩ := (inferInstance : Nonempty M)
  obtain ⟨scale, hpos, hdiv, hrescale⟩ := K.exists_diverging_surfaceRescalings
  choose base hbase hbound using fun k : ℕ =>
    K.exists_reducedLength_minimizer_le_one reference (hpos k)
  exact ⟨{
    reference := reference
    scale := scale
    scale_pos := hpos
    scale_tendsto := hdiv
    rescaling := fun k => Classical.choice (hrescale k)
    base := base
    base_minimizing := hbase
    base_reduced_length_bound := fun k => by simpa using hbound k }⟩

end PoincareConjecture.AncientKappaSolution
