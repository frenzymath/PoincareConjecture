import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Pullback.SpatialDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.MetricDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

universe u v

namespace PoincareConjecture.MovingSpacetimeGauge

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

def spatialMetricForm (e : MovingSpacetimeGauge F T C) (t : T.Point) (x : C) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  letI : NormedSpace ℝ (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  letI : NormedAddCommGroup (F.Horizontal (e.toSpacetime (t, x))) :=
    Submodule.normedAddCommGroup _
  letI : NormedSpace ℝ (F.Horizontal (e.toSpacetime (t, x))) :=
    Submodule.normedSpace _
  exact (F.horizontalMetric.inner (e.toSpacetime (t, x))).bilinearComp
    (e.spatialDifferential t x) (e.spatialDifferential t x)

theorem spatialDifferential_apply_smoothAt (e : MovingSpacetimeGauge F T C)
    (t : T.Point) {V : (x : C) → TangentSpace (𝓡 n) x} {x : C}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (V y)) x) :
    ContMDiffAt (𝓡 n) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal)
        (e.toSpacetime (t, y)) (e.spatialDifferential t y (V y))) x := by
  have he : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y => e.toSpacetime (t, y)) :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hd : ContMDiffAt (𝓡 n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun y => TotalSpace.mk' (SpacetimeModelVector n)
        (E := (TangentSpace (spacetimeModel n) : F.Point → Type _))
        (e.toSpacetime (t, y))
        (mfderiv (𝓡 n) (spacetimeModel n) (fun z => e.toSpacetime (t, z)) y (V y))) x :=
    ((he x).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      (b₁ := id) (b₂ := fun y : C => e.toSpacetime (t, y)) hV (he x)
  have hp : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun w : TangentBundle (spacetimeModel n) F.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) w.proj
          (F.horizontalProjection w.proj w.2)) := F.horizontalProjection_smooth
  apply ((hp _).comp x hd).congr_of_eventuallyEq
  exact Eventually.of_forall fun y => rfl

theorem spatialMetricForm_smooth (e : MovingSpacetimeGauge F T C) (t : T.Point) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        x (e.spatialMetricForm t x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  apply contMDiffAt_clm_of_apply
  intro w
  let E := EuclideanSpace ℝ (Fin n)
  let a := trivializationAt E (TangentSpace (𝓡 n) : C → Type _) x
  have hx : x ∈ a.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hfield (z : E) : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y : C => TotalSpace.mk' E y (a.symmL ℝ y z)) x := by
    have hc : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun y : C => TotalSpace.mk' E (E := Bundle.Trivial C E) y z) x := by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := z)⟩
    exact (a.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞) hx).clm_bundle_apply hc
  have he : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y => e.toSpacetime (t, y)) :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have h := ((F.horizontalMetric.contMDiff _).comp x (he x)).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial F.Point ℝ)
    (e.spatialDifferential_apply_smoothAt t (hfield v))
    (e.spatialDifferential_apply_smoothAt t (hfield w))
  have hh := (contMDiffAt_totalSpace.mp h).2
  apply hh.congr_of_eventuallyEq
  filter_upwards [a.open_baseSet.mem_nhds hx] with y hy
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial C ℝ) hy hy (by simp)]
  simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, spatialMetricForm, ContinuousLinearMap.bilinearComp_apply]
  change F.horizontalMetric.inner _ (e.spatialDifferential t y (a.symm y v))
      (e.spatialDifferential t y (a.symm y w)) =
    F.horizontalMetric.inner _ (e.spatialDifferential t y (a.symmL ℝ y v))
      (e.spatialDifferential t y (a.symmL ℝ y w))
  rw [a.symmL_apply hy, a.symmL_apply hy]

def spatialMetric (e : MovingSpacetimeGauge F T C) (t : T.Point) :
    RiemannianMetric n C where
  inner := e.spatialMetricForm t
  symm x v w := F.horizontalMetric.symm _ _ _
  pos x v hv := F.horizontalMetric.pos _ _ (fun h =>
    hv (e.spatialDifferential_injective t x (h.trans (map_zero _).symm)))
  isVonNBounded x := by
    have h := (F.horizontalMetric.isVonNBounded (e.toSpacetime (t, x))).image
      (e.spatialTangentEquiv t x).symm.toContinuousLinearMap
    apply h.subset
    intro v hv
    exact ⟨e.spatialTangentEquiv t x v, hv,
      (e.spatialTangentEquiv t x).symm_apply_apply v⟩
  contMDiff := e.spatialMetricForm_smooth t

theorem spatialMetric_inner (e : MovingSpacetimeGauge F T C) (t : T.Point)
    (x : C) (v w : TangentSpace (𝓡 n) x) :
    (e.spatialMetric t).inner x v w =
      F.horizontalMetric.inner (e.toSpacetime (t, x))
        (e.spatialTangentEquiv t x v) (e.spatialTangentEquiv t x w) := rfl

end

end PoincareConjecture.MovingSpacetimeGauge
