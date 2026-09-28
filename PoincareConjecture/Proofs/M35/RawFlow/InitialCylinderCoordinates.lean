import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderContractions
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M35.Thm12_28.ScalarOperatorPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g : RiemannianMetric 3 StandardCapSpace} (C : StandardCylindricalEnd g)

theorem initialEndChart_contMDiffAt (q : UnitTwoSphere) {p : StandardCapSpace}
    (hp : 0 < (cylinderCoordinateEquiv p).2) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (C.coordinate ∘ cylinderChart q) p := by
  have hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ C.coordinate
      (cylinderChart q p) := C.coordinate_smooth.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioi).mem_nhds
          ⟨mem_univ _, (neg_lt_zero.mpr C.collar_pos).trans hp⟩)
  exact hc.comp p (cylinderChart_contMDiff q p)

theorem initialEndChart_metric (q : UnitTwoSphere) {p : StandardCapSpace}
    (hp : 0 < (cylinderCoordinateEquiv p).2) (v w : StandardCapSpace) :
    (cylinderEuclideanMetric 0 (by norm_num)).inner p v w =
      g.inner (C.coordinate (cylinderChart q p))
        (mfderiv (𝓡 3) (𝓡 3) (C.coordinate ∘ cylinderChart q) p v)
        (mfderiv (𝓡 3) (𝓡 3) (C.coordinate ∘ cylinderChart q) p w) := by
  have hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ C.coordinate
      (cylinderChart q p) := C.coordinate_smooth.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioi).mem_nhds
          ⟨mem_univ _, (neg_lt_zero.mpr C.collar_pos).trans hp⟩)
  rw [mfderiv_comp p (hc.mdifferentiableAt (by simp))
    ((cylinderChart_contMDiff q p).mdifferentiableAt (by simp))]
  change cylinderEuclideanCoefficients 0 p v w =
    g.inner (C.coordinate (cylinderChart q p))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.coordinate (cylinderChart q p)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (cylinderChart q) p v))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.coordinate (cylinderChart q p)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (cylinderChart q) p w))
  rw [C.metric_pullback (cylinderChart q p) hp.le,
    mfderiv_cylinderChart q p v, mfderiv_cylinderChart q p w]
  dsimp only [standardCylinderInner, cylinderChart]
  rw [sphere_chart_pullback_inner_at, cylinderEuclideanCoefficients_apply]
  ring

theorem initialEndChart_mfderiv_invertible (q : UnitTwoSphere) {p : StandardCapSpace}
    (hp : 0 < (cylinderCoordinateEquiv p).2) :
    (mfderiv (𝓡 3) (𝓡 3) (C.coordinate ∘ cylinderChart q) p).IsInvertible := by
  let L : StandardCapSpace →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 3) (𝓡 3) (C.coordinate ∘ cylinderChart q) p
  have hzero (v : StandardCapSpace) (hv : L v = 0) : v = 0 := by
    by_contra hn
    have hpos := (cylinderEuclideanMetric 0 (by norm_num)).pos p v hn
    rw [initialEndChart_metric C q hp v v] at hpos
    change 0 < g.inner (C.coordinate (cylinderChart q p)) (L v) (L v) at hpos
    simp only [hv, map_zero, lt_self_iff_false] at hpos
  have hi : Function.Injective L := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hvw, sub_self]
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hi).toContinuousLinearEquiv, rfl⟩

theorem initialEnd_scalar_norm (D : LeviCivitaData g) (q : UnitTwoSphere)
    {s : ℝ} (hs : 0 < s) :
    D.scalarCurvature (C.coordinate (q, s)) = 1 ∧
      D.curvatureTensorNorm (C.coordinate (q, s)) = 1 := by
  let p : StandardCapSpace := cylinderCoordinateEquiv.symm (0, s)
  let f := C.coordinate ∘ cylinderChart q
  let D0 := cylinderEuclideanConnection 0 (by norm_num)
  have hp : 0 < (cylinderCoordinateEquiv p).2 := by
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply] using hs
  have heq : f p = C.coordinate (q, s) := by
    dsimp only [f, Function.comp_def, cylinderChart, p]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    refine Prod.ext ?_ rfl
    change (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 = q
    rw [← sphere_chart_center q]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv (mem_chart_source _ q)
  have hnear : ∀ᶠ z : StandardCapSpace in 𝓝 p, 0 < (cylinderCoordinateEquiv z).2 :=
    (continuous_snd.comp cylinderCoordinateEquiv.continuous).continuousAt.eventually
      (eventually_gt_nhds hp)
  have hinv := hnear.mono (fun z hz => initialEndChart_mfderiv_invertible C q hz)
  have hmetric := hnear.mono (fun z hz => initialEndChart_metric C q hz)
  have hscalar := scalarCurvature_eq_pullback_euclidean D0 D
    (initialEndChart_contMDiffAt C q hp) hinv hmetric
  have hnorm := LeviCivitaData.curvatureTensorNorm_eq_pullback_euclidean D0 D
    (initialEndChart_contMDiffAt C q hp) hinv hmetric
  have hs0 := cylinder_scalarCurvature_center 0 (by norm_num) D0 q s
  have hn0 := cylinder_curvatureTensorNorm_center 0 (by norm_num) D0 q s
  change D0.scalarCurvature p = D.scalarCurvature (f p) at hscalar
  change D0.curvatureTensorNorm p = D.curvatureTensorNorm (f p) at hnorm
  rw [heq] at hscalar hnorm
  constructor
  · exact hscalar.symm.trans (by simpa only [sub_zero, div_one] using hs0)
  · exact hnorm.symm.trans (by simpa only [sub_zero, div_one] using hn0)

end PoincareConjecture.M35.Uniqueness
