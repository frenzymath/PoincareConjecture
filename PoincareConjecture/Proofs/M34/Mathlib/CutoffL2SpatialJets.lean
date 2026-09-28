import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Uniqueness
import PoincareConjecture.Proofs.M34.Mathlib.CutoffCoordinateEnergyLimit
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateEnergyZero












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open Poincare.Analysis.Calculus

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι]



noncomputable def cutoffCoordinateEnergy (q : F →L[ℝ] EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (h : EuclideanSpace ℝ (Fin n) → F) : ℝ :=
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  ∑ i, ∫ x, (φ x * q (h x) i) ^ 2



theorem cutoffCoordinateEnergy_nonneg (q : F →L[ℝ] EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (h : EuclideanSpace ℝ (Fin n) → F) :
    0 ≤ cutoffCoordinateEnergy q φ h := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _




theorem tendsto_zero_of_cutoff_energy
    [FiniteDimensional ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (q : F →L[ℝ] EuclideanSpace ℝ ι) (hq : Function.Injective q)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U)
    (hbound : LocallyEventuallyBoundedDerivatives U f)
    (hL : Tendsto (fun k => cutoffCoordinateEnergy q φ (f k)) atTop (𝓝 0))
    {x : EuclideanSpace ℝ (Fin n)} (hx : φ x ≠ 0) :
    Tendsto (fun k => f k x) atTop (𝓝 0) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  have hxφ : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hx)
  obtain ⟨B, hB0, hBall⟩ :=
    norm_iteratedFDeriv_le_on_compact hU f hf hbound hφc.isCompact hφU 0
  have hnorm (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ tsupport φ) :
      ‖f k y‖ ≤ B := by
    simpa [norm_iteratedFDeriv_zero] using hBall k y hy
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨S⟩ := exists_smoothSubsequenceExtraction hU (fun k => f (ns k))
    (fun k => hf (ns k)) (by
      intro K hK hKU m
      obtain ⟨C, hC⟩ := hbound K hK hKU m
      exact ⟨C, hns.eventually hC⟩)
  have hjet0 := S.iteratedFDeriv_tendsto_uniformlyOn 0 (tsupport φ) hφc.isCompact hφU
  have hval : TendstoUniformlyOn (fun j => f (ns (S.subsequence j))) S.limit
      atTop (tsupport φ) := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet0
  have hE : Tendsto (fun j => cutoffCoordinateEnergy q φ (f (ns (S.subsequence j))))
      atTop (𝓝 (cutoffCoordinateEnergy q φ S.limit)) := by
    simpa [cutoffCoordinateEnergy] using
      tendsto_cutoff_coordinate_energy (μ := volume) hU q hφ hφc hφU
        (fun j => (hf (ns (S.subsequence j))).continuousOn) hB0
        (fun j y hy => hnorm (ns (S.subsequence j)) y hy)
        (fun y hy => hval.tendsto_at hy)
  have hE0 : Tendsto (fun j => cutoffCoordinateEnergy q φ (f (ns (S.subsequence j))))
      atTop (𝓝 0) :=
    hL.comp (hns.comp S.subsequence_strictMono.tendsto_atTop)
  have henergy0 : cutoffCoordinateEnergy q φ S.limit = 0 :=
    tendsto_nhds_unique hE hE0
  have hvan : ∀ y, φ y ≠ 0 → (q ∘ S.limit) y = 0 :=
    (finite_coordinate_energy_eq_zero_iff hU
      (q.continuous.comp_continuousOn S.limit_contDiffOn.continuousOn)
      hφ hφc hφU).mp (by simpa [cutoffCoordinateEnergy] using henergy0)
  have hlim0 : S.limit x = 0 :=
    hq ((hvan x hx).trans q.map_zero.symm)
  refine ⟨S.subsequence, ?_⟩
  simpa [hlim0] using hval.tendsto_at hxφ



theorem tendstoUniformlyOn_iteratedFDeriv_of_cutoff_energy
    [FiniteDimensional ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (q : F →L[ℝ] EuclideanSpace ℝ ι) (hq : Function.Injective q)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {f : ℕ → EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U)
    (hbound : LocallyEventuallyBoundedDerivatives U f)
    (hL : Tendsto (fun k => cutoffCoordinateEnergy q φ (f k)) atTop (𝓝 0))
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKφ : K ⊆ {y | φ y ≠ 0}) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k)) 0 atTop K := by
  let Ω : Set (EuclideanSpace ℝ (Fin n)) := {y | φ y ≠ 0}
  have hΩ : IsOpen Ω := (isClosed_singleton.preimage hφ).isOpen_compl
  have hΩU : Ω ⊆ U := fun y hy =>
    hφU (subset_tsupport φ (Function.mem_support.mpr hy))
  have hpoint : ∀ y ∈ Ω, Tendsto (fun k => f k y) atTop (𝓝 0) :=
    fun y hy => tendsto_zero_of_cutoff_energy hU q hq hφ hφc hφU hf hbound hL hy
  have hsmooth : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) Ω :=
    Eventually.of_forall fun k => (hf k).mono hΩU
  have hboundΩ : LocallyEventuallyBoundedDerivatives Ω f :=
    fun A hA hAΩ l => hbound A hA (hAΩ.trans hΩU) l
  simpa [iteratedFDeriv_zero] using
    tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth hΩ hpoint hsmooth
      hboundΩ m hK hKφ




theorem tendstoUniformlyOn_iteratedFDeriv_of_cutoff_energy_Icc
    [FiniteDimensional ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (q : F →L[ℝ] EuclideanSpace ℝ ι) (hq : Function.Injective q)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {T : ℝ} {H : ℕ → ℝ → EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ k t, t ∈ Icc (0 : ℝ) T → ContDiffOn ℝ ∞ (H k t) U)
    (hbound : ∀ K, IsCompact K → K ⊆ U → ∀ m : ℕ, ∃ M : ℝ,
      ∀ k t, t ∈ Icc (0 : ℝ) T → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (H k t) x‖ ≤ M)
    (hL : TendstoUniformlyOn (fun k t => cutoffCoordinateEnergy q φ (H k t))
      (fun _ => 0) atTop (Icc (0 : ℝ) T))
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKφ : K ⊆ {y | φ y ≠ 0}) :
    ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (H k t) x‖ < ε := by
  intro ε hε
  by_contra hfail
  push Not at hfail
  have hfreq : ∃ᶠ k in atTop, ∃ t ∈ Icc (0 : ℝ) T, ∃ x ∈ K,
      ε ≤ ‖iteratedFDeriv ℝ m (H k t) x‖ :=
    frequently_atTop.mpr fun N => hfail N
  obtain ⟨js, hjs, hjsP⟩ := exists_seq_forall_of_frequently hfreq
  choose t ht using hjsP
  choose x hx using fun k => (ht k).2
  let g : ℕ → EuclideanSpace ℝ (Fin n) → F := fun k => H (js k) (t k)
  have hfg : ∀ k, ContDiffOn ℝ ∞ (g k) U :=
    fun k => hf (js k) (t k) (ht k).1
  have hboundg : LocallyEventuallyBoundedDerivatives U g := by
    intro A hA hAU l
    obtain ⟨M, hM⟩ := hbound A hA hAU l
    exact ⟨M, Eventually.of_forall fun k y hy => hM (js k) (t k) (ht k).1 y hy⟩
  have hLg : Tendsto (fun k => cutoffCoordinateEnergy q φ (g k)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hL) δ hδ)
    filter_upwards [hjs.eventually (eventually_ge_atTop N)] with k hk
    simpa [g, dist_comm] using hN (js k) hk (t k) (ht k).1
  have hjet := tendstoUniformlyOn_iteratedFDeriv_of_cutoff_energy
    hU q hq hφ hφc hφU hfg hboundg hLg m hK hKφ
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hjet) ε hε)
  have hdist : ‖iteratedFDeriv ℝ m (g N) (x N)‖ < ε := by
    have := hN N le_rfl (x N) (hx N).1
    rwa [dist_comm, dist_eq_norm, Pi.zero_apply, sub_zero] at this
  exact (hx N).2.not_gt hdist

end PoincareConjecture.M34
