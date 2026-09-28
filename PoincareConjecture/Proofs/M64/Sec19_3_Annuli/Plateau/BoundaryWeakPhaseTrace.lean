import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceConvergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakBoundaryTrace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




theorem m64WeakPhase_lower_trace_tendsto
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hU : ∀ j, MemLp (f j) 2 mu)
    (hV : ∀ j, MemLp (fun p => fderiv ℝ (f j) p
      (EuclideanSpace.single (1 : Fin 2) 1)) 2 mu)
    {u V : Lp ℝ 2 mu}
    (hu : Tendsto (fun j => (hU j).toLp (f j)) atTop (𝓝 u))
    (hv : WeakConverges (fun j => (hV j).toLp (fun p => fderiv ℝ (f j) p
      (EuclideanSpace.single (1 : Fin 2) 1))) V)
    {C : ℝ} (hC : ∀ j, (∫ p in S,
      (fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) ≤ C)
    (b : ℝ → ℝ) (hb : MemLp b 2 nu)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x)) :
    ∃ hT : ∀ j, MemLp (fun x => f j (annulusPoint x 0)) 2 nu,
      Tendsto (fun j => (hT j).toLp (fun x => f j (annulusPoint x 0)))
        atTop (𝓝 (hb.toLp b)) := by
  obtain ⟨hT, hcauchy⟩ := m64Annulus_lower_trace_cauchySeq f hf hC hU hu.cauchySeq
  obtain ⟨T, hlimT⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hae : (T : ℝ → ℝ) =ᵐ[nu] b := by
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp T).integrable (by norm_num)).locallyIntegrable
      (hb.integrable (by norm_num)).locallyIntegrable
    intro psi hpsi hcompact
    let phi := fun p : LoopPlane => psi (p 0) * (1 - p 1)
    let dphi := fun p : LoopPlane =>
      fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1)
    have hphi : ContDiff ℝ 1 phi :=
      ((hpsi.of_le (show (1 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
        (contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)
    have htop (x : ℝ) : phi (annulusPoint x 1) = 0 := by simp [phi, annulusPoint]
    have hbottom (x : ℝ) : phi (annulusPoint x 0) = psi x := by simp [phi, annulusPoint]
    have hp : MemLp phi 2 mu := by
      apply (memLp_two_iff_integrable_sq hphi.continuous.aestronglyMeasurable).mpr
      exact (hphi.continuous.pow 2).continuousOn.integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset
    have hdc : Continuous dphi :=
      (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdp : MemLp dphi 2 mu := by
      apply (memLp_two_iff_integrable_sq hdc.aestronglyMeasurable).mpr
      exact (hdc.pow 2).continuousOn.integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset
    have hps : MemLp psi 2 nu :=
      (hpsi.continuous.memLp_of_hasCompactSupport hcompact).mono_measure
        Measure.restrict_le_self
    let A := testIntegral (F := ℝ) phi hp
    let B := testIntegral (F := ℝ) dphi hdp
    let D := testIntegral (F := ℝ) psi hps
    have hseq (j : ℕ) :
        A ((hV j).toLp (fun p => fderiv ℝ (f j) p
          (EuclideanSpace.single (1 : Fin 2) 1))) + B ((hU j).toLp (f j)) =
        -D ((hT j).toLp (fun x => f j (annulusPoint x 0))) := by
      have h := m64Annulus_vertical_green_identity (hf j) hphi
      simp only [htop, hbottom, zero_smul, zero_sub, integral_neg] at h
      simpa only [A, B, D, testIntegral_toLp, smul_eq_mul, dphi] using h
    have hl : Tendsto (fun j =>
        A ((hV j).toLp (fun p => fderiv ℝ (f j) p
          (EuclideanSpace.single (1 : Fin 2) 1))) + B ((hU j).toLp (f j)))
        atTop (𝓝 (A V + B u)) :=
      (hv A).add ((B.continuous.tendsto u).comp hu)
    have hr : Tendsto (fun j =>
        A ((hV j).toLp (fun p => fderiv ℝ (f j) p
          (EuclideanSpace.single (1 : Fin 2) 1))) + B ((hU j).toLp (f j)))
        atTop (𝓝 (-D T)) := by
      simpa only [hseq, Function.comp_apply] using ((D.continuous.tendsto T).comp hlimT).neg
    have heq := tendsto_nhds_unique hl hr
    have hg := hgreen phi hphi htop
    simp only [hbottom] at hg
    change A V + B u = -D T at heq
    simp only [A, B, D, testIntegral_apply, smul_eq_mul, dphi] at heq
    simp only [smul_eq_mul]
    linarith
  have hTb : T = hb.toLp b := by
    apply Lp.ext
    exact hae.trans hb.coeFn_toLp.symm
  exact ⟨hT, hTb ▸ hlimT⟩

end PoincareConjecture
