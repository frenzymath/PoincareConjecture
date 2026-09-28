import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem contDiffAt_chartField_radialVariation
    {e : EuclideanSpace ℝ (Fin n) → M} (v w : EuclideanSpace ℝ (Fin n))
    {t : ℝ} {a : M}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (t • v))
    (ha : e (t • v) ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞ (chartField (fun s : ℝ => e (s • v)) a
      (fun τ => mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun s : ℝ => e (τ • (v + s • w))) 0 1)) t := by
  let c := extChartAt (𝓡 n) a
  let q := c ∘ e
  let V : ℝ → EuclideanSpace ℝ (Fin n) := fun s => s • fderiv ℝ q (s • v) w
  have hq : ContDiffAt ℝ ∞ q (t • v) :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using ha)).comp _ he)
  have hline : ContinuousAt (fun s : ℝ => s • v) t := by fun_prop
  have hnear : ∀ᶠ s : ℝ in 𝓝 t,
      MDifferentiableAt (𝓡 n) (𝓡 n) e (s • v) ∧ e (s • v) ∈ c.source := by
    have hdiff := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (he.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    have hsource := he.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) a).mem_nhds ha)
    filter_upwards [hline (hdiff.and hsource)] with s hs
    exact ⟨hs.1.mdifferentiableAt (by simp), hs.2⟩
  have hVnear : chartField (fun s : ℝ => e (s • v)) a
      (fun τ => mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun s : ℝ => e (τ • (v + s • w))) 0 1) =ᶠ[𝓝 t] V := by
    filter_upwards [hnear] with s hs
    have hd := mfderiv_comp (s • v)
      (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hs.2)) hs.1
    rw [mfderiv_eq_fderiv] at hd
    change mfderiv (𝓡 n) (𝓡 n) c (e (s • v))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (s • (v + r • w))) 0 1) = V s
    rw [radialVariation_field_eq v w s hs.1]
    have hd1 := congrArg (fun L => L (s • w)) hd
    change fderiv ℝ q (s • v) (s • w) =
      mfderiv (𝓡 n) (𝓡 n) c (e (s • v))
        (mfderiv (𝓡 n) (𝓡 n) e (s • v) (s • w)) at hd1
    rw [← hd1]
    exact map_smul _ _ _
  have hV : ContDiffAt ℝ ∞ V t :=
    contDiffAt_id.smul (((hq.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).comp (f := fun s : ℝ => s • v) t (by fun_prop))
  exact hV.congr_of_eventuallyEq hVnear

end PoincareConjecture.RiemannianMetric
