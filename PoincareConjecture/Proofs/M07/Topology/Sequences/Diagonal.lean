import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Sequences












namespace Poincare

open Filter Set
open scoped Topology



theorem exists_strictMono_forall_le_of_eventually
    {P : ℕ → ℕ → Prop} (hP : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k j, j ≤ k → P j (φ k) := by
  classical
  choose N hN using fun j => eventually_atTop.1 (hP j)
  let φ : ℕ → ℕ := fun k => Nat.rec (N 0) (fun j m => max (m + 1) (N (j + 1))) k
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun k =>
    lt_of_lt_of_le (Nat.lt_succ_self (φ k)) (le_max_left _ _)
  have hNφ (k : ℕ) : N k ≤ φ k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  exact ⟨φ, hφ, fun k j hjk => hN j (φ k) ((hNφ j).trans (hφ.monotone hjk))⟩



theorem exists_strictMono_tendsto_of_eventually_mem_isCompact
    {X : ℕ → Type*} [∀ j, TopologicalSpace (X j)]
    [∀ j, FirstCountableTopology (X j)]
    (u : ∀ j, ℕ → X j) (K : ∀ j, Set (X j))
    (hK : ∀ j, IsCompact (K j))
    (hu : ∀ j, ∀ᶠ k in atTop, u j k ∈ K j) :
    ∃ a : ∀ j, X j, (∀ j, a j ∈ K j) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ j, Tendsto (u j ∘ φ) atTop (𝓝 (a j)) := by
  choose N hN using fun j => eventually_atTop.1 (hu j)
  let v : ℕ → ∀ j, X j := fun k j => u j (max k (N j))
  have hv : ∀ k, v k ∈ {f : ∀ j, X j | ∀ j, f j ∈ K j} :=
    fun k j => hN j _ (le_max_right k (N j))
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_pi_infinite hK).tendsto_subseq hv
  refine ⟨a, ha, φ, hφ, fun j => ?_⟩
  apply ((tendsto_pi_nhds.mp hlim) j).congr'
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (N j))] with k hk
  simp only [v, Function.comp_apply, max_eq_left hk]



theorem exists_strictMono_tendsto_forall_le_of_eventually
    {X : ℕ → Type*} [∀ j, TopologicalSpace (X j)]
    [∀ j, FirstCountableTopology (X j)]
    (u : ∀ j, ℕ → X j) (K : ∀ j, Set (X j))
    (hK : ∀ j, IsCompact (K j))
    (hu : ∀ j, ∀ᶠ k in atTop, u j k ∈ K j)
    {P : ℕ → ℕ → Prop} (hP : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ a : ∀ j, X j, (∀ j, a j ∈ K j) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ j, Tendsto (u j ∘ φ) atTop (𝓝 (a j))) ∧
        ∀ k j, j ≤ k → P j (φ k) := by
  obtain ⟨ψ, hψ, hPψ⟩ := exists_strictMono_forall_le_of_eventually hP
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    exists_strictMono_tendsto_of_eventually_mem_isCompact
      (fun j => u j ∘ ψ) K hK (fun j => hψ.tendsto_atTop.eventually (hu j))
  exact ⟨a, ha, ψ ∘ φ, hψ.comp hφ, hlim,
    fun k j hjk => hPψ (φ k) j (hjk.trans (hφ.id_le k))⟩

end Poincare
