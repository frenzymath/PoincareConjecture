import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness
















set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

private theorem exists_strictMono_eventually_mem_nested_tails
    (s : ℕ → ℕ → ℕ) (hs : ∀ i, StrictMono (s i))
    (hstep : ∀ i n, ∃ k, n ≤ k ∧ s (i + 1) n = s i k) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i N, ∀ᶠ j : ℕ in atTop, ∃ k, N ≤ k ∧ σ j = s i k := by
  have hrows (i j : ℕ) (hij : i ≤ j) (n : ℕ) :
      ∃ k, n ≤ k ∧ s j n = s i k := by
    induction j, hij using Nat.le_induction generalizing n with
    | base => exact ⟨n, le_rfl, rfl⟩
    | succ j hij ih =>
      obtain ⟨k, hnk, hk⟩ := hstep j n
      obtain ⟨l, hkl, hl⟩ := ih k
      exact ⟨l, hnk.trans hkl, hk.trans hl⟩
  let σ : ℕ → ℕ := fun j => s (j + 1) j
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro j
    obtain ⟨k, hjk, hk⟩ := hstep (j + 1) (j + 1)
    change s (j + 1) j < s (j + 1 + 1) (j + 1)
    rw [hk]
    exact hs (j + 1) ((Nat.lt_succ_self j).trans_le hjk)
  refine ⟨σ, hσ, fun i N => ?_⟩
  filter_upwards [eventually_ge_atTop (max i N)] with j hj
  have hij : i ≤ j + 1 :=
    ((le_max_left i N).trans hj).trans (Nat.le_succ j)
  obtain ⟨k, hjk, hk⟩ := hrows i (j + 1) hij j
  exact ⟨k, ((le_max_right i N).trans hj).trans hjk, hk⟩





theorem exists_common_smoothSubsequenceExtraction
    {d : ℕ → ℕ} {E : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    {Ω : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d i)))}
    (hΩ : ∀ i, IsOpen (Ω i))
    (f : (i : ℕ) → ℕ → EuclideanSpace ℝ (Fin (d i)) → E i)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) (Ω i))
    (hbound : ∀ i, LocallyEventuallyBoundedDerivatives (Ω i) (f i)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ F : (i : ℕ) → EuclideanSpace ℝ (Fin (d i)) → E i,
        (∀ i, ContDiffOn ℝ ∞ (F i) (Ω i)) ∧
        ∀ (i m : ℕ) (K : Set (EuclideanSpace ℝ (Fin (d i)))),
          IsCompact K → K ⊆ Ω i →
            TendstoUniformlyOn
              (fun j x ↦ iteratedFDeriv ℝ m (f i (σ j)) x)
              (iteratedFDeriv ℝ m (F i)) atTop K := by
  classical
  let step (i : ℕ) (σ : {σ : ℕ → ℕ // StrictMono σ}) :
      SmoothSubsequenceExtraction (Ω i) (fun j => f i (σ.val j)) :=
    Classical.choice (exists_smoothSubsequenceExtraction (hΩ i)
      (fun j => f i (σ.val j)) (fun j => hf i (σ.val j)) (by
        intro K hK hKΩ m
        obtain ⟨B, hB⟩ := hbound i K hK hKΩ m
        exact ⟨B, σ.property.tendsto_atTop.eventually hB⟩))
  let row : ℕ → {σ : ℕ → ℕ // StrictMono σ} := fun i =>
    Nat.rec ⟨id, strictMono_id⟩
      (fun i σ => ⟨σ.val ∘ (step i σ).subsequence,
        σ.property.comp (step i σ).subsequence_strictMono⟩) i
  have hrow_succ (i n : ℕ) :
      (row (i + 1)).val n =
        (row i).val ((step i (row i)).subsequence n) := rfl
  obtain ⟨σ, hσ, htail⟩ := exists_strictMono_eventually_mem_nested_tails
    (fun i => (row i).val) (fun i => (row i).property) (fun i n =>
      ⟨(step i (row i)).subsequence n,
        (step i (row i)).subsequence_strictMono.id_le n, hrow_succ i n⟩)
  refine ⟨σ, hσ, fun i => (step i (row i)).limit,
    fun i => (step i (row i)).limit_contDiffOn, ?_⟩
  intro i m K hK hKΩ V hV
  have hlim := (step i (row i)).iteratedFDeriv_tendsto_uniformlyOn m K hK hKΩ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim V hV)
  filter_upwards [htail (i + 1) N] with j hj
  obtain ⟨k, hNk, hjk⟩ := hj
  simpa only [hjk, hrow_succ] using hN k hNk

end Poincare.Analysis.Calculus
