import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveL2Trace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SliceStrongCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

omit [CompleteSpace E] [InnerProductSpace ℝ E] in


theorem m64Annulus_memLp_two_slices {u : LoopPlane → E} (hu : MemLp u 2 mu) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      MemLp (fun x => u (annulusPoint x s)) 2 (volume.restrict (Icc (0 : ℝ) curvePeriod)) := by
  have hp := hu.comp_measurePreserving m64AnnulusPoint_measurePreserving
  have hs := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  filter_upwards [hp.aestronglyMeasurable.prodMk_right, hs.prod_left_ae] with s hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi




theorem m64Annulus_continuous_slices_of_strong_approximation
    (f : ℕ → LoopPlane → E) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (u v : LoopPlane → E) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu)
    (hval : Tendsto (fun j => ∫ p in S, ‖f j p - u p‖ ^ 2) atTop (𝓝 0))
    (hder : Tendsto (fun j => ∫ p in S,
      ‖fderiv ℝ (f j) p (EuclideanSpace.single (0 : Fin 2) 1) - v p‖ ^ 2) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ∃ W : ℝ → E, ContinuousOn W (Icc (0 : ℝ) curvePeriod) ∧
        W =ᵐ[volume.restrict (Icc (0 : ℝ) curvePeriod)] (fun x => u (annulusPoint x s)) ∧
        TendstoUniformlyOn (fun j x => f (k j) (annulusPoint x s)) W
          atTop (Icc (0 : ℝ) curvePeriod) := by
  let d := fun j p => fderiv ℝ (f j) p (EuclideanSpace.single (0 : Fin 2) 1)
  have hd (j : ℕ) : Continuous (d j) :=
    ((hf j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hfl (j : ℕ) : MemLp (f j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hdl (j : ℕ) : MemLp (d j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hd j).aestronglyMeasurable).mpr
    exact ((hd j).norm.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  let F := fun j (i : Fin 2) => if i = 0 then f j else d j
  let U := fun i : Fin 2 => if i = 0 then u else v
  have hint (j : ℕ) (i : Fin 2) : IntegrableOn (fun p => ‖F j i p - U i p‖ ^ 2) S volume := by
    have hh : MemLp (F j i - U i) 2 mu := by
      dsimp only [F, U]
      split_ifs
      · exact (hfl j).sub hu
      · exact (hdl j).sub hv
    exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  have hlim (i : Fin 2) : Tendsto (fun j => ∫ p in S, ‖F j i p - U i p‖ ^ 2) atTop (𝓝 0) := by
    fin_cases i
    · simpa [F, U] using hval
    · simpa [F, U, d] using hder
  obtain ⟨k, hk, hslice⟩ := m64Annulus_strong_slice_subsequence F U hint hlim
  refine ⟨k, hk, ?_⟩
  filter_upwards [hslice, m64Annulus_memLp_two_slices hu, m64Annulus_memLp_two_slices hv]
    with s hs hus hvs
  have hpoint : Continuous (fun x => annulusPoint x s) := by unfold annulusPoint; fun_prop
  apply m64Curve_continuous_trace_of_l2_approximation
    (fun j x => f (k j) (annulusPoint x s)) (fun j x => d (k j) (annulusPoint x s))
    (fun j => (hd (k j)).comp hpoint)
    (fun j x => ((hf (k j)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x))
    (by unfold curvePeriod; positivity) (fun x => u (annulusPoint x s))
    (fun x => v (annulusPoint x s)) hus hvs
  · simpa [F, U] using hs 0
  · simpa [F, U] using hs 1

end PoincareConjecture
