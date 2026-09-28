import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Evolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarPositivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Endpoint

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [CompactSpace M] [SecondCountableTopology M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem scalarEntropy_eq_zero_of_backward_limit (K : AncientKappaSolution 2 M)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atBot)
    (hlim : Tendsto (fun k => SurfaceEntropy.scalarEntropy (K.flow.connection (a k)))
      atTop (𝓝 0)) {t : ℝ} (ht : t < 0) :
    SurfaceEntropy.scalarEntropy (K.flow.connection t) = 0 := by
  have hpos : ∀ s ∈ interior (Iic (0 : ℝ)), ∀ x,
      0 < (K.flow.connection s).scalarCurvature x := by
    intro s hs x
    exact K.scalarCurvature_pos_surface s (mem_Iic.mp (interior_subset hs)) x
  have hmono := K.flow.antitoneOn_scalarEntropy_surface (convex_Iic 0) hpos
  rw [interior_Iic] at hmono
  apply le_antisymm
  · apply ge_of_tendsto hlim
    filter_upwards [ha.eventually (eventually_lt_atBot t)] with k hk
    exact hmono (lt_trans hk ht) ht hk.le
  · exact SurfaceEntropy.scalarEntropy_nonneg _
      (K.scalarCurvature_pos_surface t ht.le)

theorem roundCertificate_of_backward_entropy_limit (K : AncientKappaSolution 2 M)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atBot)
    (hlim : Tendsto (fun k => SurfaceEntropy.scalarEntropy (K.flow.connection (a k)))
      atTop (𝓝 0)) : TwoDimensionalAncientRoundCertificate K := by
  have hround (t : ℝ) (ht : t < 0) :
      ConstantPositiveSectionalCurvature (K.flow.metric t) (K.flow.connection t) := by
    have hpos := K.scalarCurvature_pos_surface t ht.le
    apply (constantPositiveSectionalCurvature_iff_scalarCurvature _).mpr
    exact ⟨SurfaceEntropy.meanScalar (K.flow.connection t),
      SurfaceEntropy.meanScalar_pos _ hpos,
      (SurfaceEntropy.scalarEntropy_eq_zero_iff _ hpos).mp
        (K.scalarEntropy_eq_zero_of_backward_limit ha hlim ht)⟩
  refine ⟨inferInstance, fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht | rfl
  · exact hround t ht
  · exact K.round_at_zero_of_round_negative hround

end PoincareConjecture.AncientKappaSolution
