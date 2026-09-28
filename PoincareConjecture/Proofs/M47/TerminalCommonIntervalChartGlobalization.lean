import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoordinateMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {ι : Type*} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
  (d : M → N)
  (a : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
  (b : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞)
  (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
  (hUb : ∀ i, MapsTo (fun x => d ((a i).symm x)) (U i) (b i).source)
  (hcover : ∀ x : M, ∃ i, x ∈ (a i).source ∧ a i x ∈ U i)
  (hsmooth : ∀ i, ContDiffOn ℝ ∞ (fun x => b i (d ((a i).symm x))) (U i))

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
include a b U hU hUb hcover hsmooth in


theorem terminalCommonInterval_smooth_of_coordinate_rows :
    ContMDiff (𝓡 3) (𝓡 3) ∞ d := by
  intro x
  obtain ⟨i, hx, hxU⟩ := hcover x
  let F := fun z => b i (d ((a i).symm z))
  have ha := (a i).contMDiffOn_toFun.contMDiffAt ((a i).open_source.mem_nhds hx)
  have hF : ContMDiffAt (𝓡 3) (𝓡 3) ∞ F (a i x) :=
    ((hsmooth i).contDiffAt ((hU i).mem_nhds hxU)).contMDiffAt
  have hb := (b i).contMDiffOn_invFun.contMDiffAt
    ((b i).open_target.mem_nhds ((b i).map_source (hUb i hxU)))
  apply (hb.comp x (hF.comp x ha)).congr_of_eventuallyEq
  filter_upwards [(a i).open_source.mem_nhds hx,
    ha.continuousAt.tendsto.eventually ((hU i).mem_nhds hxU)] with y hy hyU
  have hai : (a i).symm (a i y) = y := (a i).toPartialEquiv.left_inv hy
  have hdy : d y ∈ (b i).source := by simpa only [hai] using hUb i hyU
  change d y = (b i).symm (b i (d ((a i).symm (a i y))))
  rw [hai]
  exact ((b i).toPartialEquiv.left_inv hdy).symm

include hU hUb hcover hsmooth in


theorem terminalCommonInterval_metric_of_coordinate_rows
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (hmetric : ∀ i x, x ∈ U i → ∀ v w : E,
      k.pullbackCoefficients (b i).symm (b i (d ((a i).symm x)))
          (fderiv ℝ (fun z => b i (d ((a i).symm z))) x v)
          (fderiv ℝ (fun z => b i (d ((a i).symm z))) x w) =
        g.pullbackCoefficients (a i).symm x v w) :
    ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = k.inner (d x)
        (mfderiv (𝓡 3) (𝓡 3) d x v) (mfderiv (𝓡 3) (𝓡 3) d x w) := by
  have hd := terminalCommonInterval_smooth_of_coordinate_rows d a b U hU hUb hcover hsmooth
  intro x v w
  obtain ⟨i, hx, hxU⟩ := hcover x
  let F := fun z => b i (d ((a i).symm z))
  have hF : DifferentiableAt ℝ F (a i x) :=
    ((hsmooth i).contDiffAt ((hU i).mem_nhds hxU)).differentiableAt (by simp)
  have hb := ((b i).contMDiffOn_invFun.contMDiffAt
    ((b i).open_target.mem_nhds ((b i).map_source (hUb i hxU)))).mdifferentiableAt (by simp)
  have heq : (b i).symm ∘ F =ᶠ[𝓝 (a i x)] d ∘ (a i).symm := by
    filter_upwards [(hU i).mem_nhds hxU] with y hy
    exact (b i).toPartialEquiv.left_inv (hUb i hy)
  have hcoeff (v' w' : E) : k.pullbackCoefficients (d ∘ (a i).symm) (a i x) v' w' =
      g.pullbackCoefficients (a i).symm (a i x) v' w' :=
    (k.pullbackCoefficients_comp_of_eventuallyEq hb hF heq v' w').symm.trans
      (hmetric i (a i x) hxU v' w')
  have hlocal := (a i).symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ ((a i).map_source hx)
  have hsurj : Function.Surjective (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x)) :=
    (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  obtain ⟨v', hv⟩ := hsurj v
  obtain ⟨w', hw⟩ := hsurj w
  have hai : (a i).symm (a i x) = x := (a i).toPartialEquiv.left_inv hx
  have hchain := mfderiv_comp (a i x)
    ((hd ((a i).symm (a i x))).mdifferentiableAt (by simp))
    (hlocal.mdifferentiableAt (by simp))
  have hm := hcoeff v' w'
  change k.inner (d ((a i).symm (a i x)))
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ (a i).symm) (a i x) v')
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ (a i).symm) (a i x) w') =
    g.inner ((a i).symm (a i x))
      (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x) v')
      (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x) w') at hm
  rw [hchain] at hm
  change k.inner (d ((a i).symm (a i x)))
      (mfderiv (𝓡 3) (𝓡 3) d ((a i).symm (a i x))
        (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x) v'))
      (mfderiv (𝓡 3) (𝓡 3) d ((a i).symm (a i x))
        (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x) w')) =
    g.inner ((a i).symm (a i x))
      (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x) v')
      (mfderiv (𝓡 3) (𝓡 3) (a i).symm (a i x) w') at hm
  rw [hv, hw] at hm
  convert! hm.symm using 1 <;> rw [hai]

omit d hUb hcover hsmooth in
include hU in


theorem terminalCommonInterval_diffeomorph_of_coordinate_rows
    (d : M ≃ₜ N) (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (hUb : ∀ i, MapsTo (fun x => d ((a i).symm x)) (U i) (b i).source)
    (hcover : ∀ x : M, ∃ i, x ∈ (a i).source ∧ a i x ∈ U i)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (fun x => b i (d ((a i).symm x))) (U i))
    (hmetric : ∀ i x, x ∈ U i → ∀ v w : E,
      k.pullbackCoefficients (b i).symm (b i (d ((a i).symm x)))
          (fderiv ℝ (fun z => b i (d ((a i).symm z))) x v)
          (fderiv ℝ (fun z => b i (d ((a i).symm z))) x w) =
        g.pullbackCoefficients (a i).symm x v w) :
    ∃ I : Diffeomorph (𝓡 3) (𝓡 3) M N ∞,
      (I : M → N) = d ∧ (I.symm : N → M) = d.symm ∧
      ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
        g.inner x v w = k.inner (I x)
          (mfderiv (𝓡 3) (𝓡 3) I x v) (mfderiv (𝓡 3) (𝓡 3) I x w) := by
  have hd := terminalCommonInterval_smooth_of_coordinate_rows d a b U hU hUb hcover hsmooth
  have hinner := terminalCommonInterval_metric_of_coordinate_rows d a b U hU hUb hcover
    hsmooth g k hmetric
  have hi : ContMDiff (𝓡 3) (𝓡 3) ∞ d.symm := by
    intro y
    have h := Poincare.contMDiffAt_of_local_left_inverse (hd (d.symm y))
      (g.mfderiv_bijective_of_pullback_eq k (d.symm y)
        (fun v w => (hinner (d.symm y) v w).symm))
      (Filter.Eventually.of_forall d.symm_apply_apply)
    simpa only [d.apply_symm_apply] using h
  exact ⟨{ toEquiv := d.toEquiv, contMDiff_toFun := hd, contMDiff_invFun := hi },
    rfl, rfl, hinner⟩

end PoincareConjecture.M47
