import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Construction.MetricCombination
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.MetricSurgery

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "TX" => TangentSpace (𝓡 3) (M := X)
local notation "TY" => TangentSpace (𝓡 3) (M := Y)

noncomputable def metricPullbackForm (g : RiemannianMetric 3 Y) (f : X → Y) (x : X) :
    TX x →L[ℝ] TX x →L[ℝ] ℝ :=
  ((mfderiv (𝓡 3) (𝓡 3) f x).precomp ℝ).comp
    ((g.inner (f x)).comp (mfderiv (𝓡 3) (𝓡 3) f x))

omit [IsManifold (𝓡 3) ∞ X] in
theorem metricPullbackForm_apply (g : RiemannianMetric 3 Y) (f : X → Y)
    (x : X) (v w : TX x) :
    metricPullbackForm g f x v w =
      g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := rfl

omit [IsManifold (𝓡 3) ∞ X] in
theorem metricPullbackForm_nonneg (g : RiemannianMetric 3 Y) (f : X → Y)
    (x : X) (v : TX x) : 0 ≤ metricPullbackForm g f x v v :=
  metric_inner_nonneg g (f x) _

set_option backward.isDefEq.respectTransparency false in
theorem metricPullbackForm_coordinates (g : RiemannianMetric 3 Y) (f : X → Y)
    {x₀ x : X}
    (hx : x ∈ (trivializationAt E TX x₀).baseSet)
    (hy : f x ∈ (trivializationAt E TY (f x₀)).baseSet) :
    ContinuousLinearMap.inCoordinates E TX (E →L[ℝ] ℝ) (fun z => TX z →L[ℝ] ℝ)
      x₀ x x₀ x (metricPullbackForm g f x) =
      let A := inTangentCoordinates (𝓡 3) (𝓡 3) id f (mfderiv (𝓡 3) (𝓡 3) f) x₀ x
      let B := ContinuousLinearMap.inCoordinates E TY (E →L[ℝ] ℝ)
        (fun z => TY z →L[ℝ] ℝ) (f x₀) (f x) (f x₀) (f x) (g.inner (f x))
      (A.precomp ℝ).comp (B.comp A) := by
  let ex := trivializationAt E TX x₀
  let ey := trivializationAt E TY (f x₀)
  let A := inTangentCoordinates (𝓡 3) (𝓡 3) id f (mfderiv (𝓡 3) (𝓡 3) f) x₀ x
  have hcancel (v : E) : ey.symm (f x) (A v) =
      mfderiv (𝓡 3) (𝓡 3) f x (ex.symm x v) := by
    change ey.symm (f x) (ey.continuousLinearMapAt ℝ (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x (ex.symmL ℝ x v))) = _
    rw [← ey.symmL_apply (R := ℝ) hy,
      ey.symmL_continuousLinearMapAt (R := ℝ) hy, ex.symmL_apply (R := ℝ) hx]
  ext v w
  change ContinuousLinearMap.inCoordinates E TX (E →L[ℝ] ℝ) (fun z => TX z →L[ℝ] ℝ)
      x₀ x x₀ x (metricPullbackForm g f x) v w =
    ContinuousLinearMap.inCoordinates E TY (E →L[ℝ] ℝ) (fun z => TY z →L[ℝ] ℝ)
      (f x₀) (f x) (f x₀) (f x) (g.inner (f x)) (A v) (A w)
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial X ℝ) hx hx (by simp),
    inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial Y ℝ) hy hy (by simp)]
  dsimp only [ex, ey] at hcancel
  simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_apply, metricPullbackForm_apply, hcancel]

set_option backward.isDefEq.respectTransparency false in
theorem metricPullbackForm_contMDiffAt (g : RiemannianMetric 3 Y)
    {f : X → Y} {x₀ : X} (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x₀) :
    ContMDiffAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (metricPullbackForm g f x)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let A := inTangentCoordinates (𝓡 3) (𝓡 3) id f (mfderiv (𝓡 3) (𝓡 3) f) x₀
  let B := fun y => ContinuousLinearMap.inCoordinates E TY (E →L[ℝ] ℝ)
    (fun z => TY z →L[ℝ] ℝ) (f x₀) y (f x₀) y (g.inner y)
  have hA : ContMDiffAt (𝓡 3) 𝓘(ℝ, E →L[ℝ] E) ∞ A x₀ := hf.mfderiv_const (by simp)
  have hB : ContMDiffAt (𝓡 3) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B (f x₀) :=
    ((contMDiffAt_hom_bundle _).mp (g.contMDiff (f x₀))).2
  have hform := (hA.clm_precomp (F₃ := ℝ)).clm_comp ((hB.comp x₀ hf).clm_comp hA)
  apply hform.congr_of_eventuallyEq
  have hx := (trivializationAt E TX x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E TX x₀)
  have hy := hf.continuousAt.preimage_mem_nhds
    ((trivializationAt E TY (f x₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E TY (f x₀)))
  filter_upwards [hx, hy] with x hx hy
  exact metricPullbackForm_coordinates g f hx hy

set_option backward.isDefEq.respectTransparency false in
noncomputable def smoothPullbackMetric (g : RiemannianMetric 3 Y) (f : X → Y)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hD : ∀ x, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x)) :
    RiemannianMetric 3 X where
  inner := metricPullbackForm g f
  symm x v w := g.symm (f x) _ _
  pos x v hv := g.pos (f x) _ (by
    intro hz
    apply hv
    apply (hD x).1
    change (mfderiv (𝓡 3) (𝓡 3) f x : E →L[ℝ] E) v =
      (mfderiv (𝓡 3) (𝓡 3) f x : E →L[ℝ] E) 0
    rw [map_zero]
    exact hz)
  isVonNBounded x := by
    let D : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) f x
    let e : E ≃L[ℝ] E := (LinearEquiv.ofBijective D.toLinearMap (hD x)).toContinuousLinearEquiv
    refine ((g.isVonNBounded (f x)).image e.symm.toContinuousLinearMap).subset ?_
    intro v hv
    refine ⟨e v, hv, e.symm_apply_apply v⟩
  contMDiff x := metricPullbackForm_contMDiffAt g (hf x)

theorem smoothPullbackMetric_inner (g : RiemannianMetric 3 Y) (f : X → Y)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hD : ∀ x, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x))
    (x : X) (v w : TX x) :
    (smoothPullbackMetric g f hf hD).inner x v w =
      g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := rfl

end PoincareConjecture.MetricSurgery
