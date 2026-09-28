import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.ScalarBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem RicciFlow.continuousOn_scalarCurvature_ancient_surface
    (F : RicciFlow 2 M (Iic 0)) (x : M) :
    ContinuousOn (fun t => (F.connection t).scalarCurvature x) (Iic 0) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    ((F.metric 0).orthonormalBasis x).reindex (finCongr hd)
  have hv : b 0 ≠ 0 := b.toBasis.ne_zero 0
  have hpos (t : ℝ) : 0 < (F.metric t).inner x (b 0) (b 0) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    exact real_inner_self_pos.mpr hv
  have hg := (Poincare.Geometry.RicciFlow.Harnack.metric_inner_contDiffOn_time
    F x (b 0) (b 0)).continuousOn
  have hRic := Poincare.Geometry.RicciFlow.Harnack.ricci_continuousOn_ancient
    F x (b 0) (b 0)
  apply ((hRic.const_mul 2).div hg (fun t _ => ne_of_gt (hpos t))).congr
  intro t _
  dsimp only [Pi.div_apply]
  rw [(F.connection t).ricci_eq_half_scalarCurvature_mul_inner]
  field_simp [ne_of_gt (hpos t)]

namespace AncientKappaSolution

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem round_at_zero_of_round_negative (K : AncientKappaSolution 2 M)
    (hround : ∀ t : ℝ, t < 0 →
      ConstantPositiveSectionalCurvature (K.flow.metric t) (K.flow.connection t)) :
    ConstantPositiveSectionalCurvature (K.flow.metric 0) (K.flow.connection 0) := by
  obtain ⟨p, hp⟩ := K.nonflat 0 le_rfl
  apply (constantPositiveSectionalCurvature_iff_scalarCurvature _).mpr
  refine ⟨(K.flow.connection 0).scalarCurvature p,
    (K.flow.connection 0).scalar_positive_of_nonflat_surface p
      (K.nonnegative_curvature_operator 0 le_rfl p) hp, ?_⟩
  intro x
  have heq : EqOn (fun t => (K.flow.connection t).scalarCurvature x)
      (fun t => (K.flow.connection t).scalarCurvature p) (Iio 0) := by
    intro t ht
    obtain ⟨r, _, hr⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
      (hround t ht)
    exact (hr x).trans (hr p).symm
  have hx := K.flow.continuousOn_scalarCurvature_ancient_surface x
  have hp := K.flow.continuousOn_scalarCurvature_ancient_surface p
  exact heq.of_subset_closure hx hp Iio_subset_Iic_self
    (by rw [closure_Iio]) (by simp)

end AncientKappaSolution

end PoincareConjecture
