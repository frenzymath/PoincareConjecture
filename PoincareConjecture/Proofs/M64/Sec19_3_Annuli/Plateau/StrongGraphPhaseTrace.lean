import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseTrace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64WeakPhase_strong_graph_trace
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    {u V : LoopPlane → ℝ} (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hval : Tendsto (fun j => eLpNorm (f j - u) 2 mu) atTop (𝓝 0))
    (hcol : Tendsto (fun j => eLpNorm (fun p => fderiv ℝ (f j) p e1 - V p) 2 mu)
      atTop (𝓝 0))
    (b : ℝ → ℝ) (hb : MemLp b 2 nu)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x)) :
    Tendsto (fun j => eLpNorm (fun x => f j (annulusPoint x 0) - b x) 2 nu)
      atTop (𝓝 0) := by
  have hF (j : ℕ) : MemLp (f j) 2 mu :=
    (memLp_two_iff_integrable_sq (hf j).continuous.aestronglyMeasurable).mpr
      (((hf j).continuous.pow 2).continuousOn.integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset)
  have hD (j : ℕ) : MemLp (fun p => fderiv ℝ (f j) p e1) 2 mu := by
    have hc := ((hf j).continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous (fun _ : LoopPlane => e1))
    exact (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      ((hc.pow 2).continuousOn.integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset)
  have hFconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hF u hu).mpr hval
  have hDconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j p => fderiv ℝ (f j) p e1) hD V hV).mpr hcol
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hDconv).exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (mem_range_self 0))
  have hbound (j : ℕ) : (∫ p in S, (fderiv ℝ (f j) p e1) ^ 2) ≤ C ^ 2 := by
    have hn : ‖(hD j).toLp (fun p => fderiv ℝ (f j) p e1)‖ ^ 2 =
        ∫ p in S, (fderiv ℝ (f j) p e1) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hD j).coeFn_toLp] with p hp
      simp only [hp, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    rw [← hn]
    exact (sq_le_sq₀ (norm_nonneg _) hC0).mpr (hC _ (mem_range_self j))
  obtain ⟨hT, htrace⟩ := m64WeakPhase_lower_trace_tendsto f hf hF hD hFconv
    (fun L => (L.continuous.tendsto (hV.toLp V)).comp hDconv) hbound b hb (by
      intro phi hphi htop
      have hvalEq : (∫ p in S, fderiv ℝ phi p e1 * hu.toLp u p) =
          ∫ p in S, fderiv ℝ phi p e1 * u p := by
        apply integral_congr_ae
        filter_upwards [hu.coeFn_toLp] with p hp
        rw [hp]
      have hcolEq : (∫ p in S, phi p * hV.toLp V p) = ∫ p in S, phi p * V p := by
        apply integral_congr_ae
        filter_upwards [hV.coeFn_toLp] with p hp
        rw [hp]
      rw [hvalEq, hcolEq]
      exact hgreen phi hphi htop)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j x => f j (annulusPoint x 0)) hT b hb).mp htrace

end PoincareConjecture
