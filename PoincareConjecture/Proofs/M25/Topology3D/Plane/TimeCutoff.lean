import Mathlib.Analysis.Calculus.ContDiff.Operations










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M25.Topology3D



theorem contDiff_timeCutoff
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K J : Set ℝ} (hK : IsClosed K) (hJ : IsOpen J) (hKJ : K ⊆ J)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hzero : ∀ z ∉ K, τ z = 0)
    {F : ℝ × V → E} (hF : ContDiffOn ℝ ∞ F (J ×ˢ univ)) :
    ContDiff ℝ ∞ (fun p : ℝ × V => τ p.1 • F p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ J
  · exact (hτ.comp contDiff_fst).contDiffAt.smul
      (hF.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
  · have hpK : p.1 ∉ K := fun h => hp (hKJ h)
    have hn : ∀ᶠ q : ℝ × V in 𝓝 p, q.1 ∉ K :=
      (hK.isOpen_compl.preimage continuous_fst).mem_nhds hpK
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × V => (0 : E)) p).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp only [hzero q.1 hq, zero_smul]

end PoincareConjecture.M25.Topology3D
