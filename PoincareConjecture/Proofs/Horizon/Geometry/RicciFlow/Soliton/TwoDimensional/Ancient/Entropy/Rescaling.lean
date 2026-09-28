import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Functional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

theorem SurfaceEntropy.scalarEntropy_eq_of_metric_eq
    {g h : RiemannianMetric 2 M} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (heq : g = h) : scalarEntropy D = scalarEntropy D' := by
  subst h
  have hR : D.scalarCurvature = D'.scalarCurvature := by
    funext x
    simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci,
      D.horizon_curvatureTensor_eq D']
  simp only [scalarEntropy, meanScalar, hR]

variable [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M} {tau : ℝ}



theorem AncientRescaling.scalarEntropy_eq_original (A : AncientRescaling K tau)
    (t : ℝ) (ht : t < 0) :
    SurfaceEntropy.scalarEntropy (A.flow.connection t) =
      SurfaceEntropy.scalarEntropy (K.flow.connection (tau * t)) := by
  calc
    _ = SurfaceEntropy.scalarEntropy
        (rescaledMetric_connection (K.flow.metric (tau * t))
          (K.flow.connection (tau * t)) (1 / tau) (one_div_pos.mpr A.tau_pos)) :=
      SurfaceEntropy.scalarEntropy_eq_of_metric_eq _ _ (A.metric_eq_rescaledMetric t ht)
    _ = _ := SurfaceEntropy.scalarEntropy_rescaled _ _ _


theorem AncientRescaling.scalarEntropy_neg_one (A : AncientRescaling K tau) :
    SurfaceEntropy.scalarEntropy (A.flow.connection (-1)) =
      SurfaceEntropy.scalarEntropy (K.flow.connection (-tau)) := by
  exact (A.scalarEntropy_eq_original (-1) (by norm_num)).trans
    (congrArg (fun t => SurfaceEntropy.scalarEntropy (K.flow.connection t)) (mul_neg_one tau))

theorem AncientRescalingSequence.scalarEntropy_rescaling_subseq
    (S : AncientRescalingSequence K) (σ : ℕ → ℕ) (k : ℕ) :
    SurfaceEntropy.scalarEntropy ((S.rescaling (σ k)).flow.connection (-1)) =
      SurfaceEntropy.scalarEntropy (K.flow.connection (-S.scale (σ k))) :=
  (S.rescaling (σ k)).scalarEntropy_neg_one



theorem AncientRescalingSequence.tendsto_scalarEntropy_original_of_rescaling
    (S : AncientRescalingSequence K) (σ : ℕ → ℕ)
    (h : Tendsto (fun k => SurfaceEntropy.scalarEntropy
      ((S.rescaling (σ k)).flow.connection (-1))) atTop (𝓝 0)) :
    Tendsto (fun k => SurfaceEntropy.scalarEntropy
      (K.flow.connection (-S.scale (σ k)))) atTop (𝓝 0) := by
  simpa only [S.scalarEntropy_rescaling_subseq] using h

end PoincareConjecture
