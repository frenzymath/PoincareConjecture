import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M60

variable {n m : ℕ} {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y]
  [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin m)
local notation "TX" => TangentSpace (𝓡 n) (M := X)
local notation "TY" => TangentSpace (𝓡 m) (M := Y)

noncomputable def metricPullbackForm (g : RiemannianMetric m Y) (f : X → Y) (x : X) :
    TX x →L[ℝ] TX x →L[ℝ] ℝ :=
  ((mfderiv (𝓡 n) (𝓡 m) f x).precomp ℝ).comp
    ((g.inner (f x)).comp (mfderiv (𝓡 n) (𝓡 m) f x))

omit [IsManifold (𝓡 n) ∞ X] in

theorem metricPullbackForm_apply (g : RiemannianMetric m Y) (f : X → Y)
    (x : X) (v w : TX x) :
    metricPullbackForm (n := n) g f x v w =
      g.inner (f x) (mfderiv (𝓡 n) (𝓡 m) f x v) (mfderiv (𝓡 n) (𝓡 m) f x w) := rfl

theorem metricPullbackForm_coordinates (g : RiemannianMetric m Y) (f : X → Y)
    {x₀ x : X}
    (hx : x ∈ (trivializationAt E TX x₀).baseSet)
    (hy : f x ∈ (trivializationAt F TY (f x₀)).baseSet) :
    ContinuousLinearMap.inCoordinates E TX (E →L[ℝ] ℝ) (fun z => TX z →L[ℝ] ℝ)
      x₀ x x₀ x (metricPullbackForm (n := n) g f x) =
      let A := inTangentCoordinates (𝓡 n) (𝓡 m) id f (mfderiv (𝓡 n) (𝓡 m) f) x₀ x
      let B := ContinuousLinearMap.inCoordinates F TY (F →L[ℝ] ℝ)
        (fun z => TY z →L[ℝ] ℝ) (f x₀) (f x) (f x₀) (f x) (g.inner (f x))
      (A.precomp ℝ).comp (B.comp A) := by
  let ex := trivializationAt E TX x₀
  let ey := trivializationAt F TY (f x₀)
  let A := inTangentCoordinates (𝓡 n) (𝓡 m) id f (mfderiv (𝓡 n) (𝓡 m) f) x₀ x
  have hcancel (v : E) : ey.symm (f x) (A v) =
      mfderiv (𝓡 n) (𝓡 m) f x (ex.symm x v) := by
    change ey.symm (f x) (ey.continuousLinearMapAt ℝ (f x)
      (mfderiv (𝓡 n) (𝓡 m) f x (ex.symmL ℝ x v))) = _
    rw [← ey.symmL_apply (R := ℝ) hy,
      ey.symmL_continuousLinearMapAt (R := ℝ) hy, ex.symmL_apply (R := ℝ) hx]
  ext v w
  change ContinuousLinearMap.inCoordinates E TX (E →L[ℝ] ℝ) (fun z => TX z →L[ℝ] ℝ)
      x₀ x x₀ x (metricPullbackForm (n := n) g f x) v w =
    ContinuousLinearMap.inCoordinates F TY (F →L[ℝ] ℝ) (fun z => TY z →L[ℝ] ℝ)
      (f x₀) (f x) (f x₀) (f x) (g.inner (f x)) (A v) (A w)
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial X ℝ) hx hx (by simp),
    inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial Y ℝ) hy hy (by simp)]
  dsimp only [ex, ey] at hcancel
  simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_apply, metricPullbackForm_apply, hcancel]

theorem metricPullbackForm_contMDiffAt (g : RiemannianMetric m Y)
    {f : X → Y} {x₀ : X} (hf : ContMDiffAt (𝓡 n) (𝓡 m) ∞ f x₀) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (metricPullbackForm (n := n) g f x)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let A := inTangentCoordinates (𝓡 n) (𝓡 m) id f (mfderiv (𝓡 n) (𝓡 m) f) x₀
  let B := fun y => ContinuousLinearMap.inCoordinates F TY (F →L[ℝ] ℝ)
    (fun z => TY z →L[ℝ] ℝ) (f x₀) y (f x₀) y (g.inner y)
  have hA : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] F) ∞ A x₀ := hf.mfderiv_const (by simp)
  have hB : ContMDiffAt (𝓡 m) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ B (f x₀) :=
    ((contMDiffAt_hom_bundle _).mp (g.contMDiff (f x₀))).2
  have hform := (hA.clm_precomp (F₃ := ℝ)).clm_comp ((hB.comp x₀ hf).clm_comp hA)
  apply hform.congr_of_eventuallyEq
  have hx := (trivializationAt E TX x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E TX x₀)
  have hy := hf.continuousAt.preimage_mem_nhds
    ((trivializationAt F TY (f x₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F TY (f x₀)))
  filter_upwards [hx, hy] with x hx hy
  exact metricPullbackForm_coordinates g f hx hy

end PoincareConjecture.M60
