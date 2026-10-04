import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareLib.Geometry.RicciFlow.Soliton.Basic
import PoincareLib.Geometry.Riemannian.Connection.Construction
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareLib.Geometry.Riemannian.Metric.ConnectedComponent
import Mathlib.Topology.Homotopy.Lifting

/-!
# Noncollapse on the Ricci-null orientation cover

Lifting almost minimizing curves shows that a Riemannian covering maps each
intrinsic ball onto its base ball. The projection is distance nonincreasing,
so calibrated Hausdorff volume and the local curvature identity transfer
static noncollapse with the same constant, including for disconnected covers.

Reference: Morgan--Tian, Claim 9.45, pp. 208--209.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] in
private theorem contMDiff_curve_lift {F : M → N}
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F)
    {γ : ℝ → N} {Γ : ℝ → M} (hΓ : Continuous Γ)
    (hlift : F ∘ Γ = γ) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 Γ := by
  intro t
  let ht := hF (Γ t)
  have hs := (ht.localInverse_contMDiffAt.of_le (by simp)).comp t
    (show ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 (F ∘ Γ) t from hlift ▸ hγ t)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hΓ.continuousAt.preimage_mem_nhds
    (ht.localInverse.open_target.mem_nhds ht.localInverse_mem_target)] with s hs
  exact (ht.localInverse_left_inv hs).symm

/-- Every intrinsic ball of a Riemannian covering projects onto the base ball. -/
theorem RiemannianMetric.image_ball_of_covering
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) {F : M → N}
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F) (hc : IsCoveringMap F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    (p : M) (r : ℝ) : F '' g.ball p r = h.ball (F p) r := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (g.edist_map_le_of_metric_pullback h hF.contMDiff hinner p x).trans_lt hx
  · intro q hq
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hq zero_lt_one
    obtain ⟨Γ, ⟨hΓ0, hΓlift⟩, _⟩ :=
      hc.existsUnique_continuousMap_lifts ⟨γ, hγ.continuous⟩ 0 p h0.symm
    have hΓsmooth := contMDiff_curve_lift hF Γ.continuous hΓlift hγ
    have hdist : g.edist p (Γ 1) ≤ g.pathELength Γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hΓsmooth.contMDiffOn hΓ0 rfl zero_le_one
    have heq : g.pathELength Γ 0 1 = h.pathELength γ 0 1 := by
      rw [g.pathELength_map_of_metric_pullback h hF.contMDiff hinner Γ hΓsmooth,
        hΓlift]
      rfl
    refine ⟨Γ 1, hdist.trans_lt (heq.trans_lt hlen), ?_⟩
    exact (congrFun hΓlift 1).trans h1

variable [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N]

/-- A metric-preserving smooth map cannot increase calibrated volume of images. -/
theorem calibratedMetricVolume_image_le_of_metric_pullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) {F : M → N}
    (hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    (s : Set M) : calibratedMetricVolume h (F '' s) ≤ calibratedMetricVolume g s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  have hLip : LipschitzWith 1 F := by
    intro x y
    change h.edist (F x) (F y) ≤ (1 : ℝ≥0∞) * g.edist x y
    simpa only [one_mul] using g.edist_map_le_of_metric_pullback h hF hinner x y
  have hmeasure : Measure.hausdorffMeasure (n : ℝ) (F '' s) ≤
      Measure.hausdorffMeasure (n : ℝ) s := by
    simpa using hLip.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) s
  exact mul_le_mul' le_rfl hmeasure

/-- Static noncollapse lifts through an actual Riemannian covering without
loss of the noncollapse constant. -/
theorem MetricKappaNoncollapsed.of_covering
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {F : M → N}
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F) (hc : IsCoveringMap F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    {κ : ℝ} (hκ : MetricKappaNoncollapsed h D' κ) :
    MetricKappaNoncollapsed g D κ := by
  refine ⟨hκ.1, fun p r hr hbound => ?_⟩
  have hball := g.image_ball_of_covering h hF hc hinner p r
  have hbase : ∀ q ∈ h.ball (F p) r, |D'.curvatureTensorNorm q| ≤ r⁻¹ ^ 2 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hball.symm ▸ hq
    rw [← D.curvatureTensorNorm_eq_of_local_isometry D' isOpen_univ
      hF.contMDiff.contMDiffOn (fun x _ => hinner x) (mem_univ x)]
    exact hbound x hx
  have hvol := calibratedMetricVolume_image_le_of_metric_pullback
    g h hF.contMDiff hinner (g.ball p r)
  rw [hball] at hvol
  exact (hκ.2 (F p) r hr hbase).trans hvol

/-- Static noncollapse restricts to an actual connected component, whose
intrinsic balls are the original ambient balls. -/
theorem MetricKappaNoncollapsed.connectedComponentMetric
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {κ : ℝ} (hκ : MetricKappaNoncollapsed g D κ) (p : M) :
    MetricKappaNoncollapsed (g.connectedComponentMetric p)
      (g.connectedComponentMetric p).leviCivitaData κ := by
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let gC := g.connectedComponentMetric p
  let DC := gC.leviCivitaData
  let incl : C → M := Subtype.val
  have hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) C
  have hinner (x : C) (v w : TangentSpace (𝓡 n) x) :
      gC.inner x v w = g.inner (incl x)
        (mfderiv (𝓡 n) (𝓡 n) incl x v) (mfderiv (𝓡 n) (𝓡 n) incl x w) := rfl
  refine ⟨hκ.1, fun x r hr hbound => ?_⟩
  have hball := g.image_ball_subtype_val isClosed_connectedComponent gC hinner x r
  have hbase : ∀ y ∈ g.ball (incl x) r, |D.curvatureTensorNorm y| ≤ r⁻¹ ^ 2 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hball.symm ▸ hy
    rw [← DC.curvatureTensorNorm_eq_of_local_isometry D isOpen_univ
      hi.contMDiff.contMDiffOn (fun z _ => hinner z) (mem_univ z)]
    exact hbound z hz
  have hvol := calibratedMetricVolume_image_le_of_metric_pullback
    gC g hi.contMDiff hinner (gC.ball x r)
  rw [hball] at hvol
  exact (hκ.2 (incl x) r hr hbase).trans hvol

namespace RicciFlow.Splitting

/-- The canonical unit Ricci-kernel metric inherits static noncollapse from
the base soliton, even when the orientation cover is disconnected. -/
theorem unitRicciKernelMetric_kappaNoncollapsed
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    {κ : ℝ} (hκ : MetricKappaNoncollapsed g D κ) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    letI := unitRicciKernelT3Space D hc
    letI : MeasurableSpace (UnitRicciKernel D) := borel (UnitRicciKernel D)
    letI : BorelSpace (UnitRicciKernel D) := ⟨rfl⟩
    MetricKappaNoncollapsed (unitRicciKernelMetric D hc)
      (unitRicciKernelMetric D hc).leviCivitaData κ := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let := unitRicciKernelT3Space D hc
  let : MeasurableSpace (UnitRicciKernel D) := borel (UnitRicciKernel D)
  let : BorelSpace (UnitRicciKernel D) := ⟨rfl⟩
  exact MetricKappaNoncollapsed.of_covering (unitRicciKernelMetric D hc).leviCivitaData D
    (unitRicciKernelProjection_isLocalDiffeomorph D hc) hc (fun _ _ _ => rfl) hκ

end RicciFlow.Splitting
end PoincareMT
