import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Pullback.Metric
import PoincareConjecture.Proofs.M12.Geometry.Manifold.ContDiff.LinearMap

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

theorem spatialDifferential_apply_joint_smoothAt (e : MovingSpacetimeGauge F T C)
    {V : (p : T.Point × C) → TangentSpace (𝓡 n) p.2} {p : T.Point × C}
    (hV : ContMDiffAt (spacetimeModel n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2 (V q)) p) :
    ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal)
        (e.toSpacetime q) (e.spatialDifferential q.1 q.2 (V q))) p := by
  have he : ContMDiff ((spacetimeModel n).prod (𝓡 n)) (spacetimeModel n) ∞
      (fun z : (T.Point × C) × C => e.toSpacetime (z.1.1, z.2)) :=
    e.smooth.comp (contMDiff_fst.fst.prodMk contMDiff_snd)
  have hd : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun q => TotalSpace.mk' (SpacetimeModelVector n)
        (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) (e.toSpacetime q)
        (mfderiv (𝓡 n) (spacetimeModel n) (fun z => e.toSpacetime (q.1, z)) q.2 (V q))) p :=
    ((he (p, p.2)).mfderiv (fun q z => e.toSpacetime (q.1, z)) Prod.snd
      contMDiffAt_snd (m := ∞) (by simp)).clm_apply_of_inCoordinates
        (b₁ := Prod.snd) (b₂ := e.toSpacetime) hV (e.smooth p)
  have hp : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun w : TangentBundle (spacetimeModel n) F.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) w.proj
          (F.horizontalProjection w.proj w.2)) := F.horizontalProjection_smooth
  apply ((hp _).comp p hd).congr_of_eventuallyEq
  exact Eventually.of_forall fun q => rfl

theorem spatialMetricForm_joint_smooth (e : MovingSpacetimeGauge F T C) :
    ContMDiff (spacetimeModel n) ((𝓡 n).prod 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : T.Point × C => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun x : C => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        p.2 (e.spatialMetricForm p.1 p.2)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  apply contMDiffAt_clm_of_apply_model
  intro v
  apply contMDiffAt_clm_of_apply_model
  intro w
  let E := EuclideanSpace ℝ (Fin n)
  let a := trivializationAt E (TangentSpace (𝓡 n) : C → Type _) p.2
  have hx : p.2 ∈ a.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hfield (z : E) : ContMDiffAt (spacetimeModel n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : T.Point × C => TotalSpace.mk' E q.2 (a.symmL ℝ q.2 z)) p := by
    have hc : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun y : C => TotalSpace.mk' E (E := Bundle.Trivial C E) y z) p.2 := by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := z)⟩
    exact ((a.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞) hx).clm_bundle_apply hc).comp p
      contMDiffAt_snd
  have h := ((F.horizontalMetric.contMDiff _).comp p (e.smooth p)).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial F.Point ℝ)
    (e.spatialDifferential_apply_joint_smoothAt (hfield v))
    (e.spatialDifferential_apply_joint_smoothAt (hfield w))
  have hh := (contMDiffAt_totalSpace.mp h).2
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuousAt_snd (a.open_baseSet.mem_nhds hx)] with q hq
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial C ℝ) hq hq (by simp)]
  simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, spatialMetricForm, ContinuousLinearMap.bilinearComp_apply]
  change F.horizontalMetric.inner _ (e.spatialDifferential q.1 q.2 (a.symm q.2 v))
      (e.spatialDifferential q.1 q.2 (a.symm q.2 w)) =
    F.horizontalMetric.inner _ (e.spatialDifferential q.1 q.2 (a.symmL ℝ q.2 v))
      (e.spatialDifferential q.1 q.2 (a.symmL ℝ q.2 w))
  rw [a.symmL_apply hq, a.symmL_apply hq]

end

end PoincareConjecture.MovingSpacetimeGauge
