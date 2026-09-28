import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Uniform
import Mathlib.Analysis.Calculus.FDeriv.Symmetric









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_fderiv_commute {f : E → F} (hf : ContDiff ℝ ∞ f)
    (v w x : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  simp only [fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using (hf.contDiffAt.isSymmSndFDerivAt
    (by simp; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) w v

theorem timeDerivative_spatialDerivative_apply {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (v : E) (p : E × ℝ) :
    timeDerivative (fun q => spatialDerivative f q v) p =
      spatialDerivative (timeDerivative f) p v := by
  change fderiv ℝ (fun q => fderiv ℝ f q (v, 0)) p (0, 1) =
    fderiv ℝ (fun q => fderiv ℝ f q (0, 1)) p (v, 0)
  exact directional_fderiv_commute hf (v, 0) (0, 1) p

theorem timeDerivative_clm_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × ℝ → G →L[ℝ] F} (hf : ContDiff ℝ ∞ f) (v : G) (p : E × ℝ) :
    timeDerivative (fun q => f q v) p = timeDerivative f p v := by
  simp [timeDerivative, fderiv_clm_apply (hf.differentiable (by simp) p)
    (differentiableAt_const _)]

theorem timeDerivative_spatialDerivative {f : E × ℝ → F}
    (hf : ContDiff ℝ ∞ f) :
    timeDerivative (spatialDerivative f) = spatialDerivative (timeDerivative f) := by
  funext p
  ext v
  rw [← timeDerivative_clm_apply (contDiff_spatialDerivative hf)]
  exact timeDerivative_spatialDerivative_apply hf v p

theorem timeDerivative_spatialDerivative_spatialDerivative_apply
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (v w : E) (p : E × ℝ) :
    timeDerivative (fun q => spatialDerivative (spatialDerivative f) q v w) p =
      spatialDerivative (spatialDerivative (timeDerivative f)) p v w := by
  have hd := contDiff_spatialDerivative hf
  have hdd := contDiff_spatialDerivative hd
  rw [timeDerivative_clm_apply (hdd.clm_apply contDiff_const),
    timeDerivative_clm_apply hdd,
    timeDerivative_spatialDerivative hd, timeDerivative_spatialDerivative hf]

theorem timeDerivative_eventuallyEq {f g : E × ℝ → F} {p : E × ℝ}
    (hfg : f =ᶠ[𝓝 p] g) : timeDerivative f =ᶠ[𝓝 p] timeDerivative g :=
  (hfg.fderiv (𝕜 := ℝ)).mono fun _ hq => congrArg (fun L => L (0, 1)) hq

theorem spatialDerivative_eventuallyEq {f g : E × ℝ → F} {p : E × ℝ}
    (hfg : f =ᶠ[𝓝 p] g) : spatialDerivative f =ᶠ[𝓝 p] spatialDerivative g :=
  (hfg.fderiv (𝕜 := ℝ)).mono fun _ hq =>
    congrArg (fun L => L.comp (ContinuousLinearMap.inl ℝ E ℝ)) hq

theorem iterate_timeDerivative_eventuallyEq {f g : E × ℝ → F} {p : E × ℝ}
    (hfg : f =ᶠ[𝓝 p] g) (k : ℕ) :
    (timeDerivative^[k]) f =ᶠ[𝓝 p] (timeDerivative^[k]) g := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using timeDerivative_eventuallyEq ih

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem timeDerivative_static_heat_equation
    {a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι × ℝ → F} (hf : ContDiff ℝ ∞ f)
    {S : Set (EuclideanSpace ℝ ι)} {J : Set ℝ} (hJ : IsOpen J)
    (hheat : ∀ x ∈ S, ∀ t ∈ J,
      timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (a x))
        (spatialDerivative (spatialDerivative f) (x, t))) :
    ∀ x ∈ S, ∀ t ∈ J,
      timeDerivative (timeDerivative f) (x, t) =
        Kernel.matrixLap (coefficientMatrix (a x))
          (spatialDerivative (spatialDerivative (timeDerivative f)) (x, t)) := by
  intro x hx t ht
  let e := EuclideanSpace.basisFun ι ℝ
  have hd := contDiff_timeDerivative hf
  have hdd := contDiff_spatialDerivative (contDiff_spatialDerivative hf)
  have he (i j : ι) : HasDerivAt
      (fun s => spatialDerivative (spatialDerivative f) (x, s) (e i) (e j))
      (spatialDerivative (spatialDerivative (timeDerivative f)) (x, t) (e i) (e j)) t := by
    have hh' := hasDerivAt_timeSlice
      (((hdd.clm_apply (contDiff_const (c := e i))).clm_apply
        (contDiff_const (c := e j))).differentiable (by simp)) x t
    rw [timeDerivative_spatialDerivative_spatialDerivative_apply hf] at hh'
    exact hh'
  have hr := HasDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
    HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
      (he i j).const_smul (coefficientMatrix (a x) i j)
  have heq : (fun s => Kernel.matrixLap (coefficientMatrix (a x))
      (spatialDerivative (spatialDerivative f) (x, s))) =ᶠ[𝓝 t]
      (fun s => timeDerivative f (x, s)) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact (hheat x hx s hs).symm
  have hr' : HasDerivAt (fun s => timeDerivative f (x, s))
      (Kernel.matrixLap (coefficientMatrix (a x))
        (spatialDerivative (spatialDerivative (timeDerivative f)) (x, t))) t := by
    have hr'' : HasDerivAt
        (fun s => Kernel.matrixLap (coefficientMatrix (a x))
          (spatialDerivative (spatialDerivative f) (x, s)))
        (Kernel.matrixLap (coefficientMatrix (a x))
          (spatialDerivative (spatialDerivative (timeDerivative f)) (x, t))) t := by
      convert hr using 1
      · ext s
        simp [Kernel.matrixLap, e]
      · rfl
    exact hr''.congr_of_eventuallyEq heq.symm
  exact (hasDerivAt_timeSlice (hd.differentiable (by simp)) x t).unique hr'

theorem iterate_timeDerivative_static_heat_equation
    {a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι × ℝ → F} (hf : ContDiff ℝ ∞ f)
    {S : Set (EuclideanSpace ℝ ι)} {J : Set ℝ} (hJ : IsOpen J)
    (hheat : ∀ x ∈ S, ∀ t ∈ J,
      timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (a x))
        (spatialDerivative (spatialDerivative f) (x, t))) (k : ℕ) :
    ContDiff ℝ ∞ ((timeDerivative^[k]) f) ∧
    ∀ x ∈ S, ∀ t ∈ J,
      timeDerivative ((timeDerivative^[k]) f) (x, t) =
        Kernel.matrixLap (coefficientMatrix (a x))
          (spatialDerivative (spatialDerivative ((timeDerivative^[k]) f)) (x, t)) := by
  induction k with
  | zero => exact ⟨hf, hheat⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨contDiff_timeDerivative ih.1, timeDerivative_static_heat_equation ih.1 hJ ih.2⟩




theorem iterate_timeDerivative_static_heat_equation_on
    {a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι × ℝ → F}
    {S : Set (EuclideanSpace ℝ ι)} {J : Set ℝ} (hS : IsOpen S) (hJ : IsOpen J)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ J))
    (hheat : ∀ x ∈ S, ∀ t ∈ J,
      timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (a x))
        (spatialDerivative (spatialDerivative f) (x, t))) (k : ℕ) :
    ContDiffOn ℝ ∞ ((timeDerivative^[k]) f) (S ×ˢ J) ∧
    ∀ x ∈ S, ∀ t ∈ J,
      timeDerivative ((timeDerivative^[k]) f) (x, t) =
        Kernel.matrixLap (coefficientMatrix (a x))
          (spatialDerivative (spatialDerivative ((timeDerivative^[k]) f)) (x, t)) := by
  have hsmooth (j : ℕ) : ContDiffOn ℝ ∞ ((timeDerivative^[j]) f) (S ×ˢ J) := by
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (ih.fderiv_of_isOpen (hS.prod hJ) (by simp)).clm_apply contDiffOn_const
  refine ⟨hsmooth k, ?_⟩
  intro x hx t ht
  obtain ⟨g, hg, _, hgf⟩ := exists_compact_smooth_extension
    (isCompact_singleton (x := (x, t))) (hS.prod hJ)
    (singleton_subset_iff.mpr (show (x, t) ∈ S ×ˢ J from ⟨hx, ht⟩)) hf
  have heq := hgf (x, t) (by simp)
  have hset : {p | g p = f p} ∈ 𝓝 x ×ˢ 𝓝 t := by
    rw [← nhds_prod_eq]
    exact heq
  obtain ⟨S', hS', J', hJ', hsub⟩ := Filter.mem_prod_iff.mp hset
  obtain ⟨V, hVS', hVo, hxV⟩ := mem_nhds_iff.mp hS'
  obtain ⟨W, hWJ', hWo, htW⟩ := mem_nhds_iff.mp hJ'
  have hlocal (y : EuclideanSpace ℝ ι) (hy : y ∈ V ∩ S) (s : ℝ) (hs : s ∈ W ∩ J) :
      g =ᶠ[𝓝 (y, s)] f := by
    filter_upwards [((hVo.inter hS).prod (hWo.inter hJ)).mem_nhds ⟨hy, hs⟩] with q hq
    exact hsub ⟨hVS' hq.1.1, hWJ' hq.2.1⟩
  have hgheat : ∀ y ∈ V ∩ S, ∀ s ∈ W ∩ J,
      timeDerivative g (y, s) = Kernel.matrixLap (coefficientMatrix (a y))
        (spatialDerivative (spatialDerivative g) (y, s)) := by
    intro y hy s hs
    have hq := hlocal y hy s hs
    rw [(timeDerivative_eventuallyEq hq).eq_of_nhds,
      (spatialDerivative_eventuallyEq (spatialDerivative_eventuallyEq hq)).eq_of_nhds]
    exact hheat y hy.2 s hs.2
  have h := (iterate_timeDerivative_static_heat_equation hg (hWo.inter hJ) hgheat k).2
    x ⟨hxV, hx⟩ t ⟨htW, ht⟩
  have hkeq := iterate_timeDerivative_eventuallyEq heq k
  rw [(timeDerivative_eventuallyEq hkeq).eq_of_nhds,
    (spatialDerivative_eventuallyEq (spatialDerivative_eventuallyEq hkeq)).eq_of_nhds] at h
  exact h

end Poincare.Parabolic.Interior
