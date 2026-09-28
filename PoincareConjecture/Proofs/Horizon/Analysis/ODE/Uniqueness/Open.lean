import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth

namespace Poincare.ODE

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_nhds_of_hasDerivAt
    {F : E → E} {γ η : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ 1 F (γ t))
    (hγ : ∀ᶠ s in 𝓝 t, HasDerivAt γ (F (γ s)) s)
    (hη : ∀ᶠ s in 𝓝 t, HasDerivAt η (F (η s)) s)
    (heq : γ t = η t) : γ =ᶠ[𝓝 t] η := by
  obtain ⟨K, S, hS, hLip⟩ := hF.exists_lipschitzOnWith
  have hmemγ : ∀ᶠ s in 𝓝 t, γ s ∈ S :=
    hγ.self_of_nhds.continuousAt.preimage_mem_nhds hS
  have hmemη : ∀ᶠ s in 𝓝 t, η s ∈ S :=
    hη.self_of_nhds.continuousAt.preimage_mem_nhds (heq ▸ hS)
  exact ODE_solution_unique_of_eventually (v := fun _ => F) (s := fun _ => S)
    (Eventually.of_forall (fun _ => hLip)) (hγ.and hmemγ) (hη.and hmemη) heq

theorem eqOn_of_hasDerivAt
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {γ η : ℝ → E} {J : Set ℝ} (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hγ : ∀ t ∈ J, γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t)
    (hη : ∀ t ∈ J, η t ∈ U ∧ HasDerivAt η (F (η t)) t)
    {a : ℝ} (ha : a ∈ J) (heq : γ a = η a) : EqOn γ η J := by
  have hlocal (t : ℝ) (ht : t ∈ J) (he : γ t = η t) : γ =ᶠ[𝓝 t] η :=
    eq_nhds_of_hasDerivAt
      ((hF.contDiffAt (hU.mem_nhds (hγ t ht).1)).of_le (by simp))
      (Filter.Eventually.mono (hJ.mem_nhds ht) fun s hs => (hγ s hs).2)
      (Filter.Eventually.mono (hJ.mem_nhds ht) fun s hs => (hη s hs).2) he
  let G : Set ℝ := {t | γ =ᶠ[𝓝 t] η}
  have hopen : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hclosed : closure G ∩ J ⊆ G := by
    intro t ht
    have hfreq : ∃ᶠ s in 𝓝 t, s ∈ G := mem_closure_iff_frequently.mp ht.1
    apply hlocal t ht.2
    exact tendsto_nhds_unique_of_frequently_eq (hγ t ht.2).2.continuousAt
      (hη t ht.2).2.continuousAt (hfreq.mono fun s hs => hs.self_of_nhds)
  have hall := hconn.subset_of_closure_inter_subset hopen ⟨a, ha, hlocal a ha heq⟩ hclosed
  exact fun t ht => (hall ht).self_of_nhds

theorem eqOn_const_of_solution_hits_equilibrium
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {γ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hγ : ∀ t ∈ J, γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t)
    {a : ℝ} (ha : a ∈ J) (hzero : F (γ a) = 0) :
    EqOn γ (fun _ => γ a) J := by
  apply eqOn_of_hasDerivAt hU hF hJ hconn hγ
    (fun t _ => ⟨(hγ a ha).1, ?_⟩) ha rfl
  simpa only [hzero] using hasDerivAt_const t (γ a)

end Poincare.ODE
