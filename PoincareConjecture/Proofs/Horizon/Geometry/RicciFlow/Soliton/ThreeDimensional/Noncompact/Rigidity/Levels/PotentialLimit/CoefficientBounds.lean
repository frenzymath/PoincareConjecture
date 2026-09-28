import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.JetBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Set (EuclideanSpace ℝ (Fin n))}

theorem LocallyEventuallyBoundedDerivatives.fderiv
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    (hf : LocallyEventuallyBoundedDerivatives Ω f) :
    LocallyEventuallyBoundedDerivatives Ω (fun k => fderiv ℝ (f k)) := by
  intro K hK hKΩ m
  simpa only [norm_iteratedFDeriv_fderiv] using hf K hK hKΩ (m + 1)

theorem LocallyEventuallyContDiff.fderiv
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    (hf : LocallyEventuallyContDiff Ω f) :
    LocallyEventuallyContDiff Ω (fun k => fderiv ℝ (f k)) := by
  intro K hK hKΩ
  filter_upwards [hf K hK hKΩ] with k ⟨U, hU, hKU, hk⟩
  exact ⟨U, hU, hKU, hk.fderiv_of_isOpen hU (by simp)⟩

theorem LocallyEventuallyBoundedDerivatives.clm
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    (hf : LocallyEventuallyBoundedDerivatives Ω f)
    (hs : LocallyEventuallyContDiff Ω f) (L : E →L[ℝ] F) :
    LocallyEventuallyBoundedDerivatives Ω (fun k x => L (f k x)) := by
  intro K hK hKΩ m
  obtain ⟨B, hB⟩ := hf K hK hKΩ m
  refine ⟨‖L‖ * B, ?_⟩
  filter_upwards [hB, hs K hK hKΩ] with k hk ⟨U, hU, hKU, hks⟩ x hx
  exact (L.norm_iteratedFDeriv_comp_left (hks.contDiffAt (hU.mem_nhds (hKU hx)))
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).trans
    (mul_le_mul_of_nonneg_left (hk x hx) (norm_nonneg L))

theorem LocallyEventuallyContDiff.clm
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    (hs : LocallyEventuallyContDiff Ω f) (L : E →L[ℝ] F) :
    LocallyEventuallyContDiff Ω (fun k x => L (f k x)) := by
  intro K hK hKΩ
  filter_upwards [hs K hK hKΩ] with k ⟨U, hU, hKU, hk⟩
  exact ⟨U, hU, hKU, L.contDiff.comp_contDiffOn hk⟩

theorem LocallyEventuallyBoundedDerivatives.prodMk
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    {g : ℕ → EuclideanSpace ℝ (Fin n) → F}
    (hf : LocallyEventuallyBoundedDerivatives Ω f)
    (hg : LocallyEventuallyBoundedDerivatives Ω g)
    (hsf : LocallyEventuallyContDiff Ω f) (hsg : LocallyEventuallyContDiff Ω g) :
    LocallyEventuallyBoundedDerivatives Ω (fun k x => (f k x, g k x)) := by
  intro K hK hKΩ m
  obtain ⟨A, hA⟩ := hf K hK hKΩ m
  obtain ⟨B, hB⟩ := hg K hK hKΩ m
  refine ⟨max A B, ?_⟩
  filter_upwards [hA, hB, hsf K hK hKΩ, hsg K hK hKΩ]
    with k hkA hkB ⟨U, hU, hKU, hkf⟩ ⟨V, hV, hKV, hkg⟩ x hx
  rw [iteratedFDeriv_prodMk (hkf.contDiffAt (hU.mem_nhds (hKU hx)))
    (hkg.contDiffAt (hV.mem_nhds (hKV hx)))
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)]
  exact (ContinuousMultilinearMap.opNorm_prod _ _).le.trans
    (max_le_max (hkA x hx) (hkB x hx))

theorem LocallyEventuallyContDiff.prodMk
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    {g : ℕ → EuclideanSpace ℝ (Fin n) → F}
    (hf : LocallyEventuallyContDiff Ω f) (hg : LocallyEventuallyContDiff Ω g) :
    LocallyEventuallyContDiff Ω (fun k x => (f k x, g k x)) := by
  intro K hK hKΩ
  filter_upwards [hf K hK hKΩ, hg K hK hKΩ]
    with k ⟨U, hU, hKU, hkf⟩ ⟨V, hV, hKV, hkg⟩
  exact ⟨U ∩ V, hU.inter hV, fun _ hx => ⟨hKU hx, hKV hx⟩,
    (hkf.mono inter_subset_left).prodMk (hkg.mono inter_subset_right)⟩

theorem LocallyEventuallyBoundedDerivatives.comp_smooth
    [FiniteDimensional ℝ E]
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    {f₀ : EuclideanSpace ℝ (Fin n) → E} {U : Set E} {g : E → F}
    (hf : LocallyEventuallyBoundedDerivatives Ω f)
    (hs : LocallyEventuallyContDiff Ω f)
    (hf₀ : ContinuousOn f₀ Ω) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo f₀ Ω U)
    (hconv : ∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn f f₀ atTop K) :
    LocallyEventuallyBoundedDerivatives Ω (fun k => g ∘ f k) := by
  intro K hK hKΩ m
  obtain ⟨T, hT, hTU, hmaps⟩ := exists_compact_target_of_tendstoUniformlyOn hK hU
    (hf₀.mono hKΩ) (hmap.mono_left hKΩ) (hconv K hK hKΩ)
  have hj (i : Fin (m + 1)) :
      ∃ C : ℝ, ∀ x ∈ T, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    apply hT.exists_bound_of_continuousOn
    intro x hx
    exact ((hg.contDiffAt (hU.mem_nhds (hTU hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)).continuousWithinAt
  choose a ha using hj
  let A := ∑ i : Fin (m + 1), max (a i) 0
  have hA (l : ℕ) (hl : l ≤ m) (x : E) (hx : x ∈ T) :
      ‖iteratedFDeriv ℝ l g x‖ ≤ A := by
    let i : Fin (m + 1) := ⟨l, by omega⟩
    exact (ha i x hx).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (a j) 0) (Finset.mem_univ i)))
  obtain ⟨B, _, hB⟩ := hf.bound_all hK hKΩ m
  refine ⟨m.factorial * A * (max B 1) ^ m, ?_⟩
  filter_upwards [hmaps, hB, hs K hK hKΩ]
    with k hkmap hkB ⟨V, hV, hKV, hks⟩ x hx
  apply norm_iteratedFDeriv_comp_le_of_contDiffAt
    (hks.contDiffAt (hV.mem_nhds (hKV hx)))
    (hg.contDiffAt (hU.mem_nhds (hTU (hkmap hx)))) m
    (fun l hl => hA l hl _ (hkmap hx))
  intro l hl hlm
  exact (hkB l hlm x hx).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hl)))

theorem LocallyEventuallyContDiff.comp_smooth
    [FiniteDimensional ℝ E]
    {f : ℕ → EuclideanSpace ℝ (Fin n) → E}
    {f₀ : EuclideanSpace ℝ (Fin n) → E} {U : Set E} {g : E → F}
    (hs : LocallyEventuallyContDiff Ω f)
    (hf₀ : ContinuousOn f₀ Ω) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo f₀ Ω U)
    (hconv : ∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn f f₀ atTop K) :
    LocallyEventuallyContDiff Ω (fun k => g ∘ f k) := by
  intro K hK hKΩ
  obtain ⟨T, _, hTU, hmaps⟩ := exists_compact_target_of_tendstoUniformlyOn hK hU
    (hf₀.mono hKΩ) (hmap.mono_left hKΩ) (hconv K hK hKΩ)
  filter_upwards [hmaps, hs K hK hKΩ] with k hkmap ⟨V, hV, hKV, hks⟩
  refine ⟨V ∩ (f k) ⁻¹' U, hks.continuousOn.isOpen_inter_preimage hV hU,
    fun x hx => ⟨hKV hx, hTU (hkmap hx)⟩, ?_⟩
  exact hg.comp (hks.mono inter_subset_left) (fun _ hx => hx.2)

theorem tendstoUniformlyOn_of_zeroJet
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℕ → X → E} {f₀ : X → E} {K : Set X}
    (h : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (f k))
      (iteratedFDeriv ℝ 0 f₀) atTop K) : TendstoUniformlyOn f f₀ atTop K := by
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → X)).comp_tendstoUniformlyOn h

end Poincare.Analysis.Calculus
