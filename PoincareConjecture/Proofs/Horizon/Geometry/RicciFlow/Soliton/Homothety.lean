import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

namespace HomotheticMetricSlice

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g h : RiemannianMetric n M} {c : ℝ}

theorem scalarCurvature (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D'.scalarCurvature x = c⁻¹ * D.scalarCurvature (E.map x) := by
  rw [← rescaledMetric_scalarCurvature g D c hc]
  exact D'.scalarCurvature_eq_of_local_isometry
    (rescaledMetric_connection g D c hc) isOpen_univ
    E.map.contMDiff.contMDiffOn (fun y _ u v => E.inner_eq y u v) (Set.mem_univ x)

theorem metricComplete [T3Space M] (E : HomotheticMetricSlice g h c)
    (hc : 0 < c) (hg : MetricComplete g) : MetricComplete h := by
  apply (RiemannianMetric.metricComplete_iff_diffeomorph
    h (rescaledMetric g c hc) E.map (fun y u v => E.inner_eq y u v)).mpr
  exact metricComplete_rescaledMetric g c hc hg

end HomotheticMetricSlice

section Surface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g h : RiemannianMetric 2 M}

theorem constantPositiveSectionalCurvature_iff_scalarCurvature
    (D : LeviCivitaData g) :
    ConstantPositiveSectionalCurvature g D ↔
      ∃ R : ℝ, 0 < R ∧ ∀ x : M, D.scalarCurvature x = R := by
  constructor
  · rintro ⟨c, hc, hsec⟩
    refine ⟨2 * c, mul_pos (by norm_num) hc, fun x => ?_⟩
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
      rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
      simp
    let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
      (g.orthonormalBasis x).reindex (finCongr hd)
    rw [D.scalarCurvature_eq_twice_sectionalCurvature x b]
    congr 1
    apply hsec x (b 0) (b 1)
    · exact b.inner_eq_ite 0 0
    · exact b.inner_eq_ite 1 1
    · exact b.inner_eq_ite 0 1
  · rintro ⟨R, hR, hscalar⟩
    refine ⟨R / 2, div_pos hR (by norm_num), fun x u v hu hv huv => ?_⟩
    rw [D.sectionalCurvature_eq_half_scalarCurvature x u v
      (by simp [hu, hv, huv]), hscalar]

theorem HomotheticMetricSlice.constantPositiveSectionalCurvature
    {c : ℝ} (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hg : ConstantPositiveSectionalCurvature g D) :
    ConstantPositiveSectionalCurvature h D' := by
  obtain ⟨R, hR, hscalar⟩ :=
    (constantPositiveSectionalCurvature_iff_scalarCurvature D).mp hg
  apply (constantPositiveSectionalCurvature_iff_scalarCurvature D').mpr
  refine ⟨c⁻¹ * R, mul_pos (inv_pos.mpr hc) hR, fun x => ?_⟩
  rw [E.scalarCurvature hc D D', hscalar]

end Surface

section ShrinkingSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem ShrinkingSolitonFlow.round_at_time {S : GradientShrinkingSolitonData 2 M}
    (G : ShrinkingSolitonFlow S)
    (hround : ConstantPositiveSectionalCurvature S.metric S.connection)
    (t : ℝ) (ht : t < 0) :
    ConstantPositiveSectionalCurvature (G.flow.metric t) (G.flow.connection t) := by
  obtain ⟨E⟩ := G.self_similar t ht
  exact E.constantPositiveSectionalCurvature (abs_pos.mpr (ne_of_lt ht))
    S.connection (G.flow.connection t) hround

end ShrinkingSurface

end PoincareConjecture
