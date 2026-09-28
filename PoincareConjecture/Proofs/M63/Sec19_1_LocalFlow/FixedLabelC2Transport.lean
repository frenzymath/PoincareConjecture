import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_fixedLabel_comp
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) {psi : ℝ → ℝ}
    (hpsi : ContDiff ℝ 2 psi) (hpos : ∀ x, 0 < deriv psi x)
    (hshift : ∀ x, psi (x + curvePeriod) = psi x + curvePeriod) :
    M63C2ShrinkingCurveOn F (fun x t => c (psi x) t) J := by
  let d := fun x t => c (psi x) t
  let B : ℝ × ℝ → ℝ × ℝ := fun z => (psi z.1, z.2)
  have hB : ContDiff ℝ 1 B :=
    ((hpsi.of_le (by norm_num)).comp contDiff_fst).prodMk contDiff_snd
  have hmap (K : Set ℝ) : MapsTo B (univ ×ˢ K) (univ ×ˢ K) :=
    fun _ hz => ⟨mem_univ _, hz.2⟩
  have hbase : ContinuousOn (fun z : ℝ × ℝ => d z.1 z.2) (univ ×ˢ J) :=
    hc.continuous.comp (s := univ ×ˢ J) (f := B)
      hB.continuous.continuousOn (hmap J)
  have hvel (t : ℝ) (ht : t ∈ J) (x : ℝ) :
      curveVelocity (n := n) (fun y => d y t) x =
        deriv psi x • curveVelocity (n := n) (fun y => c y t) (psi x) :=
    curveVelocity_comp
      ((hc.spatial_regular t ht).mdifferentiable (by norm_num) (psi x))
      ((hpsi.differentiable (by norm_num) x).hasDerivAt)
  have hcurv (t : ℝ) (ht : t ∈ J) (x : ℝ) :
      m62CurvatureVector F d t x = m62CurvatureVector F c t (psi x) :=
    curvatureVector_comp F c
      ((hc.spatial_regular t ht).mdifferentiable (by norm_num))
      (hpsi.differentiable (by norm_num)) hpos
      ((unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t ht)
        (hc.immersed t ht) (psi x)).mdifferentiableAt (by norm_num))
  have hX : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨d z.1 z.2, curveVelocity (n := n) (fun y => c y z.2) (psi z.1)⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ J) :=
    hc.velocity_continuous.comp (s := univ ×ˢ J) (f := B)
      hB.continuous.continuousOn (hmap J)
  have hscalar : Continuous (fun z : ℝ × ℝ => deriv psi z.1) :=
    (hpsi.deriv' (n := 1)).continuous.comp continuous_fst
  have hscaled : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨d z.1 z.2, deriv psi z.1 •
        curveVelocity (n := n) (fun y => c y z.2) (psi z.1)⟩ :
          TangentBundle (𝓡 n) M)) (univ ×ˢ J) := by
    intro z0 hz0
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n)) (d z0.1 z0.2)
    apply (FiberBundle.continuousWithinAt_totalSpace E _).mpr
    refine ⟨hbase z0 hz0, ?_⟩
    have hw : ContinuousWithinAt (fun z : ℝ × ℝ =>
        (e ⟨d z.1 z.2,
          curveVelocity (n := n) (fun y => c y z.2) (psi z.1)⟩).2)
        (univ ×ˢ J) z0 :=
      ((FiberBundle.continuousWithinAt_totalSpace E _).mp (hX z0 hz0)).2
    have hcoord := hscalar.continuousAt.continuousWithinAt.smul hw
    apply hcoord.congr_of_eventuallyEq_of_mem _ hz0
    have hnear : ∀ᶠ z in 𝓝[univ ×ˢ J] z0, d z.1 z.2 ∈ e.baseSet :=
      (hbase z0 hz0) (e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (d z0.1 z0.2)))
    filter_upwards [hnear] with z hz
    change (e ⟨d z.1 z.2, deriv psi z.1 •
        curveVelocity (n := n) (fun y => c y z.2) (psi z.1)⟩).2 =
      deriv psi z.1 • (e ⟨d z.1 z.2,
        curveVelocity (n := n) (fun y => c y z.2) (psi z.1)⟩).2
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hz] using
      (e.continuousLinearMapAt ℝ (d z.1 z.2)).map_smul
        (deriv psi z.1) (curveVelocity (n := n) (fun y => c y z.2) (psi z.1))
  have hH : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨d z.1 z.2, m62CurvatureVector F c z.2 (psi z.1)⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ J) :=
    hc.curvature_continuous.comp (s := univ ×ˢ J) (f := B)
      hB.continuous.continuousOn (hmap J)
  refine
    { domain_subset := hc.domain_subset
      periodic := fun t ht x => ?_
      spatial_regular := fun t ht => (hc.spatial_regular t ht).comp hpsi.contMDiff
      joint_c1 := hc.joint_c1.comp (s := univ ×ˢ interior J) (f := B)
        hB.contMDiff.contMDiffOn (hmap (interior J))
      immersed := fun t ht x => ?_
      continuous := hbase
      velocity_continuous := hscaled.congr (fun z hz => ?_)
      curvature_continuous := hH.congr (fun z hz => ?_)
      equation := fun t ht x => ?_ }
  · change c (psi (x + curvePeriod)) t = c (psi x) t
    rw [hshift x]
    exact hc.periodic t ht (psi x)
  · rw [hvel t ht x]
    exact smul_ne_zero (hpos x).ne' (hc.immersed t ht (psi x))
  · change (⟨d z.1 z.2, curveVelocity (n := n) (fun y => d y z.2) z.1⟩ :
        TangentBundle (𝓡 n) M) = _
    rw [hvel z.2 hz.2 z.1]
  · change (⟨d z.1 z.2, m62CurvatureVector F d z.2 z.1⟩ :
        TangentBundle (𝓡 n) M) = _
    rw [hcurv z.2 hz.2 z.1]
  · rw [hcurv t (interior_subset ht) x]
    exact hc.equation t ht (psi x)

theorem c2ShrinkingCurve_fixedLabel_curvature_contMDiffOn
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) {psi : ℝ → ℝ}
    (hpsi : ContDiff ℝ 2 psi) (hpos : ∀ x, 0 < deriv psi x)
    (hH : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ interior J)) :
    let d := fun x t => c (psi x) t
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ =>
        (⟨d z.1 z.2, m62CurvatureVector F d z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ interior J) := by
  let B : ℝ × ℝ → ℝ × ℝ := fun z => (psi z.1, z.2)
  have hB : ContDiff ℝ 1 B :=
    ((hpsi.of_le (by norm_num)).comp contDiff_fst).prodMk contDiff_snd
  have hcomp := hH.comp (s := univ ×ˢ interior J) (f := B)
    hB.contMDiff.contMDiffOn (fun _ hz => ⟨mem_univ _, hz.2⟩)
  apply hcomp.congr
  intro z hz
  have ht : z.2 ∈ J := interior_subset hz.2
  have hcurv := curvatureVector_comp F c
    ((hc.spatial_regular z.2 ht).mdifferentiable (by norm_num))
    (hpsi.differentiable (by norm_num)) hpos
    ((unitTangent_contMDiff_of_c2 F c (hc.spatial_regular z.2 ht)
      (hc.immersed z.2 ht) (psi z.1)).mdifferentiableAt (by norm_num))
  change (⟨c (psi z.1) z.2,
      m62CurvatureVector F (fun x t => c (psi x) t) z.2 z.1⟩ : TangentBundle (𝓡 n) M) =
    (⟨c (psi z.1) z.2, m62CurvatureVector F c z.2 (psi z.1)⟩ : TangentBundle (𝓡 n) M)
  rw [hcurv]

end PoincareConjecture.M63
