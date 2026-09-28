import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ContinuousSliceTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveTraceFundamental











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem m64Annulus_h1_slices_of_strong_approximation
    (f : ℕ → LoopPlane → E) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hperiod : ∀ j x s, f j (annulusPoint (x + curvePeriod) s) = f j (annulusPoint x s))
    (u v : LoopPlane → E) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu)
    (hval : Tendsto (fun j => ∫ p in S, ‖f j p - u p‖ ^ 2) atTop (𝓝 0))
    (hder : Tendsto (fun j => ∫ p in S,
      ‖fderiv ℝ (f j) p (EuclideanSpace.single (0 : Fin 2) 1) - v p‖ ^ 2) atTop (𝓝 0)) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      MemLp (fun x => v (annulusPoint x s)) 2 (volume.restrict (Icc (0 : ℝ) curvePeriod)) ∧
      ∃ (k : ℕ → ℕ) (W : ℝ → E), StrictMono k ∧
        ContinuousOn W (Icc (0 : ℝ) curvePeriod) ∧
        W 0 = W curvePeriod ∧
        W =ᵐ[volume.restrict (Icc (0 : ℝ) curvePeriod)] (fun x => u (annulusPoint x s)) ∧
        TendstoUniformlyOn (fun j x => f (k j) (annulusPoint x s)) W
          atTop (Icc (0 : ℝ) curvePeriod) ∧
        Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
          ‖fderiv ℝ (f (k j)) (annulusPoint x s) (EuclideanSpace.single (0 : Fin 2) 1) -
            v (annulusPoint x s)‖ ^ 2) atTop (𝓝 0) ∧
        ∀ x ∈ Icc (0 : ℝ) curvePeriod,
          W x - W 0 = ∫ t in (0 : ℝ)..x, v (annulusPoint t s) := by
  obtain ⟨k, hk, hslice⟩ := m64Annulus_continuous_slices_of_strong_approximation
    f hf u v hu hv hval hder
  let d := fun j p => fderiv ℝ (f j) p (EuclideanSpace.single (0 : Fin 2) 1)
  have hd (j : ℕ) : Continuous (d j) :=
    ((hf j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdl (j : ℕ) : MemLp (d j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hd j).aestronglyMeasurable).mpr
    exact ((hd j).norm.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hi (j : ℕ) (_ : Fin 1) : IntegrableOn (fun p => ‖d (k j) p - v p‖ ^ 2) S volume :=
    (memLp_two_iff_integrable_sq_norm ((hdl (k j)).sub hv).aestronglyMeasurable).mp
      ((hdl (k j)).sub hv)
  have hl (_ : Fin 1) : Tendsto (fun j => ∫ p in S, ‖d (k j) p - v p‖ ^ 2)
      atTop (𝓝 0) := hder.comp hk.tendsto_atTop
  obtain ⟨l, hlmono, hdslice⟩ := m64Annulus_strong_slice_subsequence
    (fun j (_ : Fin 1) => d (k j)) (fun _ => v) hi hl
  filter_upwards [hslice, hdslice, m64Annulus_memLp_two_slices hv] with s hs hds hvs
  obtain ⟨W, hW, hWu, hlim⟩ := hs
  have hT : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hend (j : ℕ) : f (k j) (annulusPoint curvePeriod s) =
      f (k j) (annulusPoint 0 s) := by simpa only [zero_add] using hperiod (k j) 0 s
  have h0 : Tendsto (fun j => f (k j) (annulusPoint curvePeriod s)) atTop (𝓝 (W 0)) := by
    simpa only [hend] using hlim.tendsto_at ⟨le_rfl, hT.le⟩
  have hends : W 0 = W curvePeriod :=
    (tendsto_nhds_unique (hlim.tendsto_at ⟨hT.le, le_rfl⟩) h0).symm
  have hlimsub : TendstoUniformlyOn (fun j x => f (k (l j)) (annulusPoint x s)) W
      atTop (Icc (0 : ℝ) curvePeriod) :=
    fun U hU => hlmono.tendsto_atTop.eventually (hlim U hU)
  refine ⟨hvs, k ∘ l, W, hk.comp hlmono, hW, hends, hWu,
    hlimsub, hds 0, ?_⟩
  have hpoint : Continuous (fun x => annulusPoint x s) := by unfold annulusPoint; fun_prop
  apply m64Curve_trace_fundamental_of_strong_approximation
    (fun j x => f (k (l j)) (annulusPoint x s)) (fun j x => d (k (l j)) (annulusPoint x s))
    (fun j => (hd (k (l j))).comp hpoint)
    (fun j x => ((hf (k (l j))).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)) hT
    (fun x => v (annulusPoint x s)) W hvs (hds 0)
  exact hlimsub

end PoincareConjecture
