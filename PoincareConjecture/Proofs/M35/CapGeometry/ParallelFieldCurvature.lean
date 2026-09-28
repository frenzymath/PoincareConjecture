import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanFields








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

noncomputable section

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

local instance parallelDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance parallelDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance parallelMetricNormedGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance parallelMetricNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance



theorem curvature_parallel_field_germ
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {Z : V → V} {x : V} (hZ : ContDiffAt ℝ ∞ Z x)
    (hparallel : ∀ᶠ y in 𝓝 x, ∀ v : V, D.connection Z y v = 0)
    (u v : V) : D.curvature x u v (Z x) = 0 := by
  have hc (a b : V) : D.connection (fun y => D.connection Z y a) x b = 0 := by
    have he : (fun y => D.connection Z y a) =ᶠ[𝓝 x] (fun _ : V => (0 : V)) :=
      hparallel.mono fun y hy => hy a
    have hd : DifferentiableAt ℝ (fun y => D.connection Z y a) x :=
      (differentiableAt_const (c := (0 : V))).congr_of_eventuallyEq he
    have hz := congrArg (fun c : V => D.euclideanConnection b c x) he.self_of_nhds
    have hzero : D.euclideanConnection b (0 : V) x = 0 := by
      simp [LeviCivitaData.euclideanConnection, D.connection_const_eq_inverse,
        metricKoszulCovector]
    rw [D.connection_eq_fderiv_add hd, he.fderiv_eq]
    simpa only [fderiv_const_apply, zero_apply, zero_add] using!
      hz.trans hzero
  have h := D.curvatureOnFields_eq_curvature_euclidean
    (contDiffAt_const (c := u)) (contDiffAt_const (c := v)) hZ
  rw [LeviCivitaData.curvatureOnFields] at h
  change D.connection (fun y => D.connection Z y v) x u -
      D.connection (fun y => D.connection Z y u) x v -
        D.connection Z x (mlieBracket (𝓡 n) (fun _ : V => u) (fun _ : V => v) x) =
    D.curvature x u v (Z x) at h
  rw [hc, hc, hparallel.self_of_nhds] at h
  simpa using h.symm



theorem curvatureTensor_parallel_field_germ
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {Z : V → V} {x : V} (hZ : ContDiffAt ℝ ∞ Z x)
    (hparallel : ∀ᶠ y in 𝓝 x, ∀ v : V, D.connection Z y v = 0)
    (u v w : V) : D.curvatureTensor x u v w (Z x) = 0 := by
  rw [LeviCivitaData.curvatureTensor, curvature_parallel_field_germ D hZ hparallel]
  simp

end

end PoincareConjecture.M35
