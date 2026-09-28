import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Curves.ArcLength
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence













open Set Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace Poincare.MetricCurves

variable {M : Type*} [MetricSpace M]

theorem exists_confined_uniform_limit
    {z y : M} {K : Set M} (hK : IsCompact K)
    {σ : ℕ → ℝ → M} {C : ℝ≥0}
    (hlip : ∀ n, LipschitzOnWith C (σ n) (Icc 0 1))
    (hstart : ∀ n, σ n 0 = z) (hfinish : ∀ n, σ n 1 = y)
    (hconf : ∀ n, MapsTo (σ n) (Icc 0 1) K) :
    ∃ (φ : ℕ → ℕ) (γ : ℝ → M), StrictMono φ ∧
      TendstoUniformlyOn (fun n => σ (φ n)) γ atTop (Icc 0 1) ∧
      LipschitzOnWith C γ (Icc 0 1) ∧
      γ 0 = z ∧ γ 1 = y ∧ MapsTo γ (Icc 0 1) K := by
  let J := Icc (0 : ℝ) 1
  let F : ℕ → J →ᵇ M := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t => σ n t, (hlip n).to_restrict.continuous⟩
  have hequi : Equicontinuous (fun n t => F n t) :=
    (LipschitzWith.uniformEquicontinuous (fun n t => F n t) C
      (fun n => (hlip n).to_restrict)).equicontinuous
  have hequi' : Equicontinuous ((↑) : range F → J → M) := by
    have heq : (fun f : range F => (fun t => F f.2.choose t)) =
        ((↑) : range F → J → M) := by
      funext f t
      exact congrArg (fun u : J →ᵇ M => u t) f.2.choose_spec
    rw [← heq]
    exact hequi.comp (fun f : range F => f.2.choose)
  have hcompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli K hK (range F)
      (by rintro f t ⟨n, rfl⟩; exact hconf n t.2) hequi'
  obtain ⟨f, _, φ, hφ, hF⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  let γ : ℝ → M := fun t => if ht : t ∈ J then f ⟨t, ht⟩ else z
  have hγ : ∀ t (ht : t ∈ J), γ t = f ⟨t, ht⟩ := fun t ht => dif_pos ht
  have hconv : TendstoUniformlyOn (fun n => σ (φ n)) γ atTop J := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hF
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformly_iff] at h
    intro ε hε
    filter_upwards [h ε hε] with n hn t ht
    rw [hγ t ht]
    have heval : (F (φ n)) ⟨t, ht⟩ = σ (φ n) t := by
      change σ (φ n) (↑(⟨t, ht⟩ : J)) = σ (φ n) t
      rfl
    simpa [heval] using hn ⟨t, ht⟩
  have hclosed : IsClosed K := hK.isClosed
  have hconf' : MapsTo γ J K := by
    intro t ht
    apply hclosed.mem_of_tendsto (hconv.tendsto_at ht)
    exact Eventually.of_forall (fun n => hconf (φ n) ht)
  have hstart' : γ 0 = z := by
    apply (isClosed_singleton : IsClosed ({z} : Set M)).mem_of_tendsto
      (hconv.tendsto_at (show (0 : ℝ) ∈ J by norm_num [J]))
    exact Eventually.of_forall (fun n => by simp [hstart (φ n)])
  have hfinish' : γ 1 = y := by
    apply (isClosed_singleton : IsClosed ({y} : Set M)).mem_of_tendsto
      (hconv.tendsto_at (show (1 : ℝ) ∈ J by norm_num [J]))
    exact Eventually.of_forall (fun n => by simp [hfinish (φ n)])
  refine ⟨φ, γ, hφ, hconv, ?_, hstart', hfinish', hconf'⟩
  intro s hs t ht
  exact le_of_tendsto
    ((hconv.tendsto_at hs).edist (hconv.tendsto_at ht))
    (Eventually.of_forall fun n => hlip (φ n) hs ht)

end Poincare.MetricCurves
