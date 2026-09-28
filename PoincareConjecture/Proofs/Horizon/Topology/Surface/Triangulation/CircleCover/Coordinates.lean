


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.GeneralPosition









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]



theorem chartCircle_subset_chart_source (x : M) {r : ℝ}
    (hsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    chartCircle x r ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
  rintro p ⟨z, hz, rfl⟩
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).map_target (hsub (sphere_subset_closedBall hz))



theorem mem_chartCircle_iff_norm_sq (x : M) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    {p : M} (hp : p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) :
    p ∈ chartCircle x r ↔
      ‖chartAt (EuclideanSpace ℝ (Fin 2)) x p - chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2 = r ^ 2 := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖e (e.symm z) - e x‖ ^ 2 = r ^ 2
    rw [e.right_inv (hsub (sphere_subset_closedBall hz)), ← dist_eq_norm, mem_sphere.mp hz]
  · intro h
    refine ⟨e p, ?_, e.left_inv hp⟩
    rw [mem_sphere, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp h



theorem coordinateSquaredRadius_regular_at_sphere
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ sphere c r) :
    ContDiffAt ℝ ∞ (fun w => ‖w - c‖ ^ 2) z ∧
      fderiv ℝ (fun w => ‖w - c‖ ^ 2) z ≠ 0 := by
  refine ⟨((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt, ?_⟩
  have hd := ((hasFDerivAt_id z).sub_const c).norm_sq
  simp only [id_eq] at hd
  have hradial : fderiv ℝ (fun w => ‖w - c‖ ^ 2) z (z - c) = 2 * r ^ 2 := by
    rw [hd.fderiv]
    rw [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, two_smul, ← two_mul,
      ← dist_eq_norm, mem_sphere.mp hz]
  intro hzero
  have heval := congrArg (fun L : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ => L (z - c)) hzero
  rw [hradial, zero_apply] at heval
  nlinarith [sq_pos_of_pos hr]



theorem chartCircle_coordinateSquaredRadius_regular (x : M) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    {p : M} (hp : p ∈ chartCircle x r) :
    ContDiffAt ℝ ∞ (fun z => ‖z - chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2)
        (chartAt (EuclideanSpace ℝ (Fin 2)) x p) ∧
      fderiv ℝ (fun z => ‖z - chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2)
        (chartAt (EuclideanSpace ℝ (Fin 2)) x p) ≠ 0 := by
  apply coordinateSquaredRadius_regular_at_sphere _ hr
  obtain ⟨z, hz, rfl⟩ := hp
  rwa [(chartAt (EuclideanSpace ℝ (Fin 2)) x).right_inv (hsub (sphere_subset_closedBall hz))]



theorem chartCircle_pair_local_level_sets (x y : M) {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) rx ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hysub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) y y) ry ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) y).target)
    {p : M} (hpx : p ∈ chartCircle x rx) (hpy : p ∈ chartCircle y ry) :
    ∃ N : Set (EuclideanSpace ℝ (Fin 2)), IsOpen N ∧
      chartAt (EuclideanSpace ℝ (Fin 2)) y p ∈ N ∧
      N ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) y).target ∧
      (∀ z ∈ N, (chartAt (EuclideanSpace ℝ (Fin 2)) y).symm z ∈ chartCircle y ry ↔
        ‖z - chartAt (EuclideanSpace ℝ (Fin 2)) y y‖ ^ 2 = ry ^ 2) ∧
      (∀ z ∈ N, (chartAt (EuclideanSpace ℝ (Fin 2)) y).symm z ∈ chartCircle x rx ↔
        ‖chartAt (EuclideanSpace ℝ (Fin 2)) x ((chartAt (EuclideanSpace ℝ (Fin 2)) y).symm z) -
          chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2 = rx ^ 2) := by
  let ex := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let ey := chartAt (EuclideanSpace ℝ (Fin 2)) y
  have hpsx := chartCircle_subset_chart_source x hxsub hpx
  have hpsy := chartCircle_subset_chart_source y hysub hpy
  refine ⟨(ey.symm.trans ex).source, (ey.symm.trans ex).open_source, ?_,
    fun _ hz => hz.1, ?_, ?_⟩
  · refine ⟨ey.map_source hpsy, ?_⟩
    change ey.symm (ey p) ∈ ex.source
    rw [ey.left_inv hpsy]
    exact hpsx
  · intro z hz
    have h := mem_chartCircle_iff_norm_sq y hry hysub (ey.map_target hz.1)
    change ey.symm z ∈ chartCircle y ry ↔ ‖ey (ey.symm z) - ey y‖ ^ 2 = ry ^ 2 at h
    rwa [ey.right_inv hz.1] at h
  · intro z hz
    exact mem_chartCircle_iff_norm_sq x hrx hxsub hz.2

variable [IsManifold (𝓡 2) ∞ M]



theorem chartCircle_pair_coordinate_derivatives (x y : M) {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) rx ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hysub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) y y) ry ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) y).target)
    {p : M} (hpx : p ∈ chartCircle x rx) (hpy : p ∈ chartCircle y ry)
    (hregular : ChartCircleRegularAlong x rx y ry) :
    let z := chartAt (EuclideanSpace ℝ (Fin 2)) y p
    let f := fun w : EuclideanSpace ℝ (Fin 2) =>
      ‖w - chartAt (EuclideanSpace ℝ (Fin 2)) y y‖ ^ 2
    let g := fun w : EuclideanSpace ℝ (Fin 2) =>
      ‖chartAt (EuclideanSpace ℝ (Fin 2)) x ((chartAt (EuclideanSpace ℝ (Fin 2)) y).symm w) -
        chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2
    f z = ry ^ 2 ∧ g z = rx ^ 2 ∧ ContDiffAt ℝ ∞ f z ∧ ContDiffAt ℝ ∞ g z ∧
      fderiv ℝ f z ≠ 0 ∧ ∃ v, fderiv ℝ f z v = 0 ∧ fderiv ℝ g z v ≠ 0 := by
  let ex := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let ey := chartAt (EuclideanSpace ℝ (Fin 2)) y
  let z := ey p
  let f := fun w : EuclideanSpace ℝ (Fin 2) => ‖w - ey y‖ ^ 2
  let g := fun w : EuclideanSpace ℝ (Fin 2) => ‖ex (ey.symm w) - ex x‖ ^ 2
  change f z = ry ^ 2 ∧ g z = rx ^ 2 ∧ ContDiffAt ℝ ∞ f z ∧ ContDiffAt ℝ ∞ g z ∧
    fderiv ℝ f z ≠ 0 ∧ ∃ v, fderiv ℝ f z v = 0 ∧ fderiv ℝ g z v ≠ 0
  have hpsx := chartCircle_subset_chart_source x hxsub hpx
  have hpsy := chartCircle_subset_chart_source y hysub hpy
  have hyinv : ey.symm z = p := ey.left_inv hpsy
  have hf : ContDiffAt ℝ ∞ f z ∧ fderiv ℝ f z ≠ 0 :=
    chartCircle_coordinateSquaredRadius_regular y hry hysub hpy
  have hg : ContDiffAt ℝ ∞ g z := by
    have hey := (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := y)).contMDiffAt
      (ey.open_target.mem_nhds (ey.map_source hpsy))
    have hex := (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := x)).contMDiffAt
      (ex.open_source.mem_nhds hpsx)
    have htransition : ContDiffAt ℝ ∞ (ex ∘ ey.symm) z := by
      have hex' : ContMDiffAt (𝓡 2) (𝓡 2) ∞ ex (ey.symm z) := hyinv.symm ▸ hex
      exact (hex'.comp z hey).contDiffAt
    exact (contDiff_norm_sq ℝ).contDiffAt.comp z (htransition.sub contDiffAt_const)
  refine ⟨(mem_chartCircle_iff_norm_sq y hry hysub hpsy).mp hpy, ?_, hf.1, hg, hf.2, ?_⟩
  · change ‖ex (ey.symm z) - ex x‖ ^ 2 = rx ^ 2
    rw [hyinv]
    exact (mem_chartCircle_iff_norm_sq x hrx hxsub hpsx).mp hpx
  · obtain ⟨w, hw, hwp⟩ := hpy
    rw [← iUnion_coordinateCircleArc_image (ey y) hry] at hw
    obtain ⟨i, t, ht, htw⟩ := mem_iUnion.mp hw
    let arc := coordinateCircleArc (ey y) ry ((i : ℝ) * Real.pi)
    have hpt : chartCircleSemicircle y ry i t = p := (congrArg ey.symm htw).trans hwp
    have htin : t ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · apply lt_of_le_of_ne ht.1
        intro heq
        exact (hregular i).1 (heq ▸ (hpt.symm ▸ hpx))
      · apply lt_of_le_of_ne ht.2
        intro heq
        exact (hregular i).2.1 (heq ▸ (hpt.symm ▸ hpx))
    have harctarget (u : ℝ) : arc u ∈ ey.target :=
      hysub (sphere_subset_closedBall (coordinateCircleArc_mem_sphere (ey y) hry.le _ u))
    have harct : arc t = z := by
      rw [← ey.right_inv (harctarget t)]
      exact congrArg ey hpt
    have harc : ContDiff ℝ ∞ arc :=
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.comp
        ((contDiff_circleMap _ _).comp (contDiff_const.add (contDiff_id.mul contDiff_const)))
    have hconst : f ∘ arc = fun _ => ry ^ 2 := by
      funext u
      have hu := coordinateCircleArc_mem_sphere (ey y) hry.le ((i : ℝ) * Real.pi) u
      change ‖arc u - ey y‖ ^ 2 = ry ^ 2
      rw [← dist_eq_norm, mem_sphere.mp hu]
    have hfd := fderiv_comp_deriv t
      (harct.symm ▸ hf.1.differentiableAt (by simp))
      (harc.differentiable (by simp)).differentiableAt
    have hgd := fderiv_comp_deriv t
      (harct.symm ▸ hg.differentiableAt (by simp))
      (harc.differentiable (by simp)).differentiableAt
    refine ⟨deriv arc t, ?_, ?_⟩
    · rw [harct] at hfd
      rw [← hfd, hconst, deriv_const]
    · rw [harct] at hgd
      rw [← hgd]
      exact (hregular i).2.2 t htin (hpt.symm ▸ hpx)

end PoincareConjecture.Topology.Surface
