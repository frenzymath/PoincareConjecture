import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.FiniteDimensional
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false

open Filter Set Function
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {d : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def LocallyEventuallyContDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) (f : ℕ → X → E) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ Ω →
    ∀ᶠ j : ℕ in atTop, ∃ U : Set X,
      IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (f j) U

theorem locallyEventuallyContDiff_of_local
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} {f : ℕ → X → E}
    (hf : ∀ x ∈ Ω, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ j in atTop, ContDiffOn ℝ ∞ (f j) U) :
    LocallyEventuallyContDiff Ω f := by
  intro K hK hKΩ
  refine hK.induction_on (p := fun S => ∀ᶠ j in atTop,
    ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ (f j) U) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun _ => ⟨∅, isOpen_empty, subset_rfl, contDiffOn_empty⟩)
  · intro S T hST hT
    exact hT.mono fun _ ⟨U, hU, hTU, hfd⟩ => ⟨U, hU, hST.trans hTU, hfd⟩
  · intro S T hS hT
    filter_upwards [hS, hT] with j ⟨U, hU, hSU, hfdU⟩ ⟨V, hV, hTV, hfdV⟩
    refine ⟨U ∪ V, hU.union hV, union_subset_union hSU hTV, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact (hfdU.contDiffAt (hU.mem_nhds hx)).contDiffWithinAt
    · exact (hfdV.contDiffAt (hV.mem_nhds hx)).contDiffWithinAt
  · intro x hx
    obtain ⟨U, hU, hxU, hfd⟩ := hf x (hKΩ hx)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU),
      hfd.mono fun _ h => ⟨U, hU, subset_rfl, h⟩⟩

private theorem exists_contDiff_extension_on_compact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : X → E) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ F : X → E, ContDiff ℝ ∞ F ∧ EqOn F f K := by
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨a, ha, had, har⟩ := hV.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨b, hb, hbd, hbr⟩ := hK.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hab (x : X) : 0 < a x + b x := by
    have hax := (har (mem_range_self x)).1
    have hbx := (hbr (mem_range_self x)).1
    by_cases hx : x ∈ K
    · have hane : a x ≠ 0 := by
        rw [← mem_support, ha]
        exact hKV hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hax hane.symm) hbx
    · have hbne : b x ≠ 0 := by
        rwa [← mem_support, hb]
      exact add_pos_of_nonneg_of_pos hax (lt_of_le_of_ne hbx hbne.symm)
  let c : X → ℝ := fun x => a x / (a x + b x)
  have hc : ContDiff ℝ ∞ c := had.div (had.add hbd) (fun x => (hab x).ne')
  have hcs : tsupport c ⊆ U := by
    apply (closure_mono (show support c ⊆ V from ?_)).trans hVU
    intro x hx
    rw [← ha]
    exact fun h => hx (by simp [c, h])
  have hcK : EqOn c (fun _ => 1) K := by
    intro x hx
    have hbx : b x = 0 := by
      rw [← notMem_support, hb]
      exact not_not_intro hx
    simp only [c, hbx, add_zero]
    exact div_self (by simpa [hbx] using (hab x).ne')
  refine ⟨fun x => c x • f x, contDiff_iff_contDiffAt.mpr (fun x => ?_), ?_⟩
  · by_cases hx : x ∈ tsupport c
    · exact hc.contDiffAt.smul ((hf x (hcs hx)).contDiffAt (hU.mem_nhds (hcs hx)))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_smul]
  · intro x hx
    simp only [hcK hx, one_smul]

theorem exists_common_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
    {X Y : ℕ → Type*}
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    [∀ i, FiniteDimensional ℝ (Y i)]
    {Ω : ∀ i, Set (X i)} (hΩ : ∀ i, IsOpen (Ω i))
    (f : ∀ i, ℕ → X i → Y i)
    (hf : ∀ i, LocallyEventuallyContDiff (Ω i) (f i))
    (hbound : ∀ i K, IsCompact K → K ⊆ Ω i →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (f i k) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f₀ : ∀ i, X i → Y i,
      (∀ i, ContDiffOn ℝ ∞ (f₀ i) (Ω i)) ∧
        ∀ i m K, IsCompact K → K ⊆ Ω i → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f i (σ k)))
          (iteratedFDeriv ℝ m (f₀ i)) atTop K := by
  classical
  let : ∀ i, LocallyCompactSpace (Ω i) := fun i => (hΩ i).locallyCompactSpace
  let A : ∀ i, CompactExhaustion (Ω i) := fun i => CompactExhaustion.choice (Ω i)
  let K : ∀ i, ℕ → Set (X i) := fun i n => Subtype.val '' A i n
  have hK (i n : ℕ) : IsCompact (K i n) := (A i |>.isCompact n).image continuous_subtype_val
  have hKΩ (i n : ℕ) : K i n ⊆ Ω i := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hKmono (i : ℕ) : Monotone (K i) := fun _ _ h => image_mono (A i |>.subset h)
  have hKn (i n : ℕ) : K i n ⊆ interior (K i (n + 1)) := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_interior.mpr
    refine ⟨Subtype.val '' interior (A i (n + 1)), image_mono interior_subset,
      (hΩ i).isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior, ?_⟩
    exact ⟨x, (A i).subset_interior_succ n hx, rfl⟩
  have hcover (i : ℕ) {C : Set (X i)} (hC : IsCompact C) (hCΩ : C ⊆ Ω i) :
      ∃ n, C ⊆ interior (K i n) := by
    have hpre : IsCompact ((Subtype.val : Ω i → X i) ⁻¹' C) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rwa [image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hCΩ)]
    obtain ⟨n, hn⟩ := (A i).exists_superset_of_isCompact hpre
    refine ⟨n + 1, fun x hx => hKn i n ?_⟩
    exact ⟨⟨x, hCΩ hx⟩, hn hx, rfl⟩
  have hsmooth (n : ℕ) : ∀ᶠ k in atTop, ∀ i : Fin (n + 1),
      ∃ U : Set (X i), IsOpen U ∧ K i n ⊆ U ∧ ContDiffOn ℝ ∞ (f i k) U :=
    eventually_all.mpr (fun i => hf i (K i n) (hK i n) (hKΩ i n))
  obtain ⟨τ, hτ, hτsmooth⟩ := Poincare.exists_strictMono_forall_le_of_eventually hsmooth
  have hext (i n : ℕ) : ∃ F : X i → Y i, ContDiff ℝ ∞ F ∧
      (i ≤ n → EqOn F (f i (τ n)) (K i n)) := by
    by_cases hi : i ≤ n
    · obtain ⟨U, hU, hKU, hfd⟩ := hτsmooth n n le_rfl ⟨i, Nat.lt_succ_of_le hi⟩
      obtain ⟨F, hF, heq⟩ := exists_contDiff_extension_on_compact (hK i n) hU hKU
        (f i (τ n)) hfd
      exact ⟨F, hF, fun _ => heq⟩
    · exact ⟨fun _ => 0, contDiff_const, fun h => (hi h).elim⟩
  choose F hF hFeq using hext
  have hjet (i : ℕ) (C : Set (X i)) (hC : IsCompact C) (hCΩ : C ⊆ Ω i) (m : ℕ) :
      ∀ᶠ n in atTop, EqOn (iteratedFDeriv ℝ m (F i n))
        (iteratedFDeriv ℝ m (f i (τ n))) C := by
    obtain ⟨N, hN⟩ := hcover i hC hCΩ
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop i] with n hn hi x hx
    have hlocal : F i n =ᶠ[𝓝 x] f i (τ n) :=
      Filter.eventuallyEq_of_mem (mem_interior_iff_mem_nhds.mp (hN hx))
        (fun y hy => hFeq i n hi (hKmono i hn hy))
    exact (hlocal.iteratedFDeriv ℝ m).self_of_nhds
  have hFbound (i : ℕ) (C : Set (X i)) (hC : IsCompact C) (hCΩ : C ⊆ Ω i) (m : ℕ) :
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ C, ‖iteratedFDeriv ℝ m (F i k) x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hbound i C hC hCΩ m
    refine ⟨B, ?_⟩
    filter_upwards [hjet i C hC hCΩ m, hτ.tendsto_atTop.eventually hB] with n hn hb x hx
    rw [hn hx]
    exact hb x hx
  obtain ⟨σ, hσ, f₀, hf₀, hlim⟩ := exists_common_smoothSubsequenceExtraction_finiteDimensional
    hΩ F (fun i n => (hF i n).contDiffOn) hFbound
  refine ⟨τ ∘ σ, hτ.comp hσ, f₀, hf₀, fun i m C hC hCΩ => ?_⟩
  exact (hlim i m C hC hCΩ).congr (hσ.tendsto_atTop.eventually (hjet i C hC hCΩ m))

theorem exists_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]
    {Ω : Set X} (hΩ : IsOpen Ω) (f : ℕ → X → E)
    (hf : LocallyEventuallyContDiff Ω f)
    (hbound : ∀ K, IsCompact K → K ⊆ Ω →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (f k) x‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f₀ : X → E,
      ContDiffOn ℝ ∞ f₀ Ω ∧
        ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f (σ k)))
          (iteratedFDeriv ℝ m f₀) atTop K := by
  obtain ⟨σ, hσ, f₀, hf₀, hlim⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
      (X := fun _ => X) (Y := fun _ => E) (fun _ => hΩ) (fun _ => f)
      (fun _ => hf) (fun _ => hbound)
  exact ⟨σ, hσ, f₀ 0, hf₀ 0, hlim 0⟩

theorem exists_smoothSubsequenceExtraction_of_locallyEventuallyContDiff
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → E)
    (hf : LocallyEventuallyContDiff Ω f)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f) :
    Nonempty (SmoothSubsequenceExtraction Ω f) := by
  obtain ⟨σ, hσ, f₀, hf₀, hlim⟩ :=
    exists_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
      hΩ f hf hbound
  exact ⟨⟨σ, hσ, f₀, hf₀, hlim⟩⟩

end Poincare.Analysis.Calculus
