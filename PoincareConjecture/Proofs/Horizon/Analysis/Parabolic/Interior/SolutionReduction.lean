import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CoefficientMatrix

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Filter Set
open scoped ContDiff Topology RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_fderiv_spatialSlice_eq_of_eventuallyEq
    {f g : E × ℝ → F} {x : E} {t : ℝ} (h : f =ᶠ[𝓝 (x, t)] g) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => g (z, t)) y) x := by
  have hs : (fun y => f (y, t)) =ᶠ[𝓝 x] (fun y => g (y, t)) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  exact (hs.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_compact_interior_heat_solution
    (a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (B : ℝ) (f : EuclideanSpace ℝ ι × ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 2 ×ˢ Ioo 0 2))
    (hPDE : ∀ x ∈ Metric.ball 0 2, ∀ t ∈ Ioc (0 : ℝ) 1,
      HasDerivAt (fun s => f (x, s))
        (∑ i : ι, ∑ j : ι,
          inner ℝ (EuclideanSpace.basisFun ι ℝ i)
            (a x (EuclideanSpace.basisFun ι ℝ j)) *
          fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, t)) y) x
            (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)) t)
    (hB : ∀ x ∈ Metric.ball 0 2, ∀ t ∈ Ioc (0 : ℝ) 1, |f (x, t)| ≤ B) :
    ∃ g : EuclideanSpace ℝ ι × ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (3 / 2) ×ˢ Icc (1 / 4 : ℝ) 1,
        g =ᶠ[𝓝 p] f) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) (3 / 2),
        ∀ t ∈ Icc (1 / 4 : ℝ) 1,
          |g (x, t)| ≤ B ∧
          timeDerivative g (x, t) = Kernel.matrixLap (coefficientMatrix (a x))
            (spatialDerivative (spatialDerivative g) (x, t))) ∧
      fderiv ℝ (fun y => fderiv ℝ (fun z => g (z, 1)) y) 0 =
        fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, 1)) y) 0 := by
  let K := Metric.closedBall (0 : EuclideanSpace ℝ ι) (3 / 2) ×ˢ Icc (1 / 4 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hU : IsOpen (Metric.ball (0 : EuclideanSpace ℝ ι) 2 ×ˢ Ioo (0 : ℝ) 2) :=
    Metric.isOpen_ball.prod isOpen_Ioo
  have hspace {x : EuclideanSpace ℝ ι} (hx : x ∈ Metric.closedBall 0 (3 / 2)) :
      x ∈ Metric.ball 0 2 := by
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hx).trans_lt (by norm_num)
  have htime {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) 1) : t ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · linarith [ht.1]
    · exact ht.2
  have hKU : K ⊆ Metric.ball 0 2 ×ˢ Ioo (0 : ℝ) 2 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hspace hx, (htime ht).1, ht.2.trans_lt (by norm_num)⟩
  obtain ⟨g, hg, hgc, hgf⟩ := exists_compact_smooth_extension hK hU hKU hf
  refine ⟨g, hg, hgc, hgf, ?_, ?_⟩
  · intro x hx t ht
    have heq := hgf (x, t) ⟨hx, ht⟩
    refine ⟨?_, ?_⟩
    · rw [heq.eq_of_nhds]
      exact hB x (hspace hx) t (htime ht)
    · have htimeEq : (fun s => g (x, s)) =ᶠ[𝓝 t] (fun s => f (x, s)) :=
        heq.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
      have hd := (hPDE x (hspace hx) t (htime ht)).congr_of_eventuallyEq htimeEq
      have hdg := hasDerivAt_timeSlice (hg.differentiable (by simp)) x t
      have hh := fderiv_fderiv_spatialSlice_eq_of_eventuallyEq heq
      rw [fderiv_fderiv_spatialSlice hg] at hh
      rw [matrixLap_coefficientMatrix, hh]
      simpa only [smul_eq_mul] using hdg.unique hd
  · apply fderiv_fderiv_spatialSlice_eq_of_eventuallyEq
    apply hgf (0, 1)
    constructor
    · exact Metric.mem_closedBall_self (by norm_num)
    · norm_num

end Poincare.Parabolic.Interior
