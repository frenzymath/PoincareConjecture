import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Witnesses

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.Weak

private theorem tendsto_eLpNorm_sub_of_diagonal
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : ℕ → X → ℝ} {u : X → ℝ} {ε : ℕ → ℝ≥0∞}
    (ha : ∀ n, MemLp (a n) 2 μ) (hb : ∀ n, MemLp (b n) 2 μ)
    (hu : MemLp u 2 μ)
    (herr : ∀ n, eLpNorm (fun x => a n x - b n x) 2 μ ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hlim : Tendsto (fun n => eLpNorm (fun x => b n x - u x) 2 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x - u x) 2 μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : eLpNorm (fun x => a n x - u x) 2 μ ≤
      ε n + eLpNorm (fun x => b n x - u x) 2 μ := by
    calc
      _ = eLpNorm (fun x => (a n x - b n x) + (b n x - u x)) 2 μ := by
        congr 1
        funext x
        ring
      _ ≤ eLpNorm (fun x => a n x - b n x) 2 μ +
          eLpNorm (fun x => b n x - u x) 2 μ :=
        eLpNorm_add_le ((ha n).sub (hb n)).aestronglyMeasurable
          ((hb n).sub hu).aestronglyMeasurable (by norm_num)
      _ ≤ _ := add_le_add (herr n) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hε.add hlim) (fun _ => bot_le) hbound

theorem MemW01p.of_tendsto_eLpNorm
    {d : ℕ} {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    {u_seq : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hseq : ∀ n, MemW01p 2 (u_seq n) O)
    (wseq : ∀ n, MemW1pWitness 2 (u_seq n) O)
    (w : MemW1pWitness 2 u O)
    (hv : Tendsto
      (fun n => eLpNorm (fun x => u_seq n x - u x) 2 (volume.restrict O))
      atTop (𝓝 0))
    (hg : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => (wseq n).weakGrad x i - w.weakGrad x i)
        2 (volume.restrict O)) atTop (𝓝 0)) :
    MemW01p 2 u O := by
  classical
  let ε : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := by
    simp [ε]
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have happ (n : ℕ) : ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧
      eLpNorm (fun x => φ x - u_seq n x) 2 (volume.restrict O) ≤ ε n ∧
      ∀ i, eLpNorm
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) - (wseq n).weakGrad x i)
        2 (volume.restrict O) ≤ ε n := by
    rcases hseq n with ⟨_, wn, φ, hφ, hc, hs, hvn, hgn⟩
    have hgn' (i : Fin d) : Tendsto
        (fun j => eLpNorm
          (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) -
            (wseq n).weakGrad x i) 2 (volume.restrict O)) atTop (𝓝 0) := by
      have heq := HasWeakPartialDeriv.ae_eq hO (wn.isWeakGrad i)
        ((wseq n).isWeakGrad i)
        ((wn.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
        (((wseq n).weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      apply (hgn i).congr'
      exact Eventually.of_forall fun j => eLpNorm_congr_ae
        (heq.mono fun x hx => congrArg
          (fun a : ℝ => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - a) hx)
    have hall : ∀ᶠ j in atTop, ∀ i : Fin d,
        eLpNorm
          (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) -
            (wseq n).weakGrad x i) 2 (volume.restrict O) ≤ ε n :=
      eventually_all.mpr fun i => (ENNReal.tendsto_nhds_zero.mp (hgn' i)) _ (hεpos n)
    obtain ⟨j, hvj, hgj⟩ :=
      ((ENNReal.tendsto_nhds_zero.mp hvn _ (hεpos n)).and hall).exists
    exact ⟨φ j, hφ j, hc j, hs j, hvj, hgj⟩
  choose φ hφ hc hs hvsmall hgsmall using happ
  have hφmem (n : ℕ) : MemLp (φ n) 2 (volume.restrict O) :=
    ((hφ n).continuous.memLp_of_hasCompactSupport (hc n)).restrict O
  refine ⟨w.memW1p, w, φ, hφ, hc, hs, ?_, ?_⟩
  · exact tendsto_eLpNorm_sub_of_diagonal hφmem (fun n => (wseq n).memLp)
      w.memLp hvsmall hεlim hv
  · intro i
    have hdmem (n : ℕ) : MemLp
        (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))
        2 (volume.restrict O) := by
      have hdcont : Continuous
          (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1)) :=
        ((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
      exact (hdcont.memLp_of_hasCompactSupport
        ((hc n).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ)))).restrict O
    exact tendsto_eLpNorm_sub_of_diagonal hdmem
      (fun n => (wseq n).weakGrad_component_memLp i) (w.weakGrad_component_memLp i)
      (fun n => hgsmall n i) hεlim (hg i)

end Poincare.Analysis.Sobolev.Weak
