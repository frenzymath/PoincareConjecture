import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanFields










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem product_metric_coefficient_fderiv
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2} {x : V}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = h.inner (cylinderCoordinateEquiv y).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (u v w : V) :
    fderiv ℝ (fun y : V => g.inner y u v) x w =
      fderiv ℝ (fun y : E2 => h.inner y
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1)
        (cylinderCoordinateEquiv x).1 (cylinderCoordinateEquiv w).1 := by
  let L := (ContinuousLinearMap.fst ℝ E2 ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  let a := (cylinderCoordinateEquiv u).1
  let b := (cylinderCoordinateEquiv v).1
  have hs : DifferentiableAt ℝ (fun y : E2 => h.inner y a b) (L x) :=
    (((h.contDiffAt_euclideanCoefficients (L x)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hd := (hs.hasFDerivAt.comp x L.hasFDerivAt).add_const
    ((cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
  have he : (fun y : V => g.inner y u v) =ᶠ[𝓝 x]
      (fun y => h.inner (L y) a b +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2) :=
    hmetric.mono fun y hy => hy u v
  rw [he.fderiv_eq]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using!
    congrArg (fun A : V →L[ℝ] ℝ => A w) hd.fderiv



theorem product_euclideanConnection
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) {x : V}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = h.inner (cylinderCoordinateEquiv y).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    (u v : V) :
    D.euclideanConnection u v x = cylinderCoordinateEquiv.symm
      (Dh.euclideanConnection (cylinderCoordinateEquiv u).1
        (cylinderCoordinateEquiv v).1 (cylinderCoordinateEquiv x).1, 0) := by
  apply (g.inner_isInvertible x).injective
  apply ContinuousLinearMap.ext
  intro w
  have h3 := D.inner_connection_const x u v w
  have h2 := Dh.inner_connection_const (cylinderCoordinateEquiv x).1
    (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1
    (cylinderCoordinateEquiv w).1
  rw [product_metric_coefficient_fderiv hmetric,
    product_metric_coefficient_fderiv hmetric,
    product_metric_coefficient_fderiv hmetric] at h3
  have hpair := hmetric.self_of_nhds
  change @Eq ℝ _ _
  rw [hpair, hpair]
  simp only [ContinuousLinearEquiv.apply_symm_apply, zero_mul, add_zero]
  rw [hpair] at h3
  change 2 * (h.inner (cylinderCoordinateEquiv x).1
      (cylinderCoordinateEquiv (D.euclideanConnection u v x)).1
      (cylinderCoordinateEquiv w).1 +
      (cylinderCoordinateEquiv (D.euclideanConnection u v x)).2 *
        (cylinderCoordinateEquiv w).2) = _ at h3
  change 2 * h.inner (cylinderCoordinateEquiv x).1
    (Dh.euclideanConnection (cylinderCoordinateEquiv u).1
      (cylinderCoordinateEquiv v).1 (cylinderCoordinateEquiv x).1)
    (cylinderCoordinateEquiv w).1 = _ at h2
  linarith only [h3, h2]



theorem product_connection_axial
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) {x : V}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = h.inner (cylinderCoordinateEquiv y).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    {Z : V → V} (hZ : DifferentiableAt ℝ Z x) (w : V) :
    fderiv ℝ (fun y => (cylinderCoordinateEquiv (Z y)).2) x w =
      (cylinderCoordinateEquiv (D.connection Z x w)).2 := by
  let L := (ContinuousLinearMap.snd ℝ E2 ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  have hd := (L.hasFDerivAt.comp x hZ.hasFDerivAt).fderiv
  have hd' : fderiv ℝ (fun y => L (Z y)) x w = L (fderiv ℝ Z x w) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun A : V →L[ℝ] ℝ => A w) hd
  change fderiv ℝ (fun y => L (Z y)) x w = _
  rw [hd', D.connection_eq_fderiv_add hZ, product_euclideanConnection D Dh hmetric]
  simp [L, ContinuousLinearMap.comp_apply]



theorem product_connection_horizontal
    {g : RiemannianMetric 3 V} {h : RiemannianMetric 2 E2}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) {x : V}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = h.inner (cylinderCoordinateEquiv y).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2)
    {Z : V → V} (hZ : DifferentiableAt ℝ Z x) (w : E2) :
    Dh.connection (fun y : E2 => (cylinderCoordinateEquiv
      (Z (cylinderCoordinateEquiv.symm (y, (cylinderCoordinateEquiv x).2)))).1)
      (cylinderCoordinateEquiv x).1 w =
        (cylinderCoordinateEquiv
          (D.connection Z x (cylinderCoordinateEquiv.symm (w, 0)))).1 := by
  let L := (ContinuousLinearMap.fst ℝ E2 ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  let A := cylinderCoordinateEquiv.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E2 ℝ)
  let phi : E2 → V := fun y => cylinderCoordinateEquiv.symm
    (y, (cylinderCoordinateEquiv x).2)
  have hphi : HasFDerivAt phi A (cylinderCoordinateEquiv x).1 :=
    cylinderCoordinateEquiv.symm.hasFDerivAt.comp _
      ((hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _))
  have hphi0 : phi (cylinderCoordinateEquiv x).1 = x :=
    cylinderCoordinateEquiv.symm_apply_apply x
  have hZphi : HasFDerivAt Z (fderiv ℝ Z x) (phi (cylinderCoordinateEquiv x).1) := by
    simpa only [hphi0] using hZ.hasFDerivAt
  have hd := L.hasFDerivAt.comp _ (hZphi.comp _ hphi)
  have hd' : fderiv ℝ (fun y => L (Z (phi y))) (cylinderCoordinateEquiv x).1 w =
      L (fderiv ℝ Z x (A w)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun B : E2 →L[ℝ] E2 => B w) hd.fderiv
  have hYs : DifferentiableAt ℝ (fun y => L (Z (phi y)))
      (cylinderCoordinateEquiv x).1 := hd.differentiableAt
  change Dh.connection (fun y => L (Z (phi y))) (cylinderCoordinateEquiv x).1 w = _
  rw [Dh.connection_eq_fderiv_add hYs, D.connection_eq_fderiv_add hZ]
  change @Eq E2 _ _
  rw [hd', product_euclideanConnection D Dh hmetric]
  simp [L, A, hphi0, ContinuousLinearMap.comp_apply]

end PoincareConjecture.M35
