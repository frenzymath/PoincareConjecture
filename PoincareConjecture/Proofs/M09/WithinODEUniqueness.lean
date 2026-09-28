import PoincareConjecture.Proofs.M09.OpenODEUniqueness
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open scoped Topology

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem openODE_eventuallyEqWithin (S : Set (ℝ × E)) (hS : IsOpen S)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ 1 V S)
    (I : Set ℝ) (hI : Set.OrdConnected I) (f g : ℝ → E)
    (t0 : ℝ) (ht0 : t0 ∈ I) (h0 : (t0, f t0) ∈ S) (heq : f t0 = g t0)
    (hfc : ContinuousWithinAt f I t0) (hgc : ContinuousWithinAt g I t0)
    (hf : ∀ᶠ t in 𝓝[I] t0, (t, f t) ∈ S ∧ HasDerivAt f (V (t, f t)) t)
    (hg : ∀ᶠ t in 𝓝[I] t0, (t, g t) ∈ S ∧ HasDerivAt g (V (t, g t)) t) :
    f =ᶠ[𝓝[I] t0] g := by
  obtain ⟨K, Q, hQ, hL⟩ := (hV.contDiffAt (hS.mem_nhds h0)).exists_lipschitzOnWith
  have hLip : ∀ t : ℝ, LipschitzOnWith K (fun x ↦ V (t, x)) {x | (t, x) ∈ Q} := by
    intro t x hx y hy
    simpa only [Prod.edist_eq, edist_self,
      max_eq_right (show 0 ≤ edist x y from bot_le)] using hL hx hy
  have hfQ : ∀ᶠ t in 𝓝[I] t0, (t, f t) ∈ Q :=
    (continuousWithinAt_id.prodMk hfc).preimage_mem_nhdsWithin hQ
  have hgQ : ∀ᶠ t in 𝓝[I] t0, (t, g t) ∈ Q := by
    apply (continuousWithinAt_id.prodMk hgc).preimage_mem_nhdsWithin
    simpa only [heq, Function.id_def] using hQ
  obtain ⟨ε, hε, hdata⟩ := Metric.mem_nhdsWithin_iff.mp (hf.and (hg.and (hfQ.and hgQ)))
  rw [Real.ball_eq_Ioo] at hdata
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [Metric.ball_mem_nhds t0 hε] with t ht htI
  rw [Real.ball_eq_Ioo] at ht
  by_cases horder : t0 ≤ t
  · have hsegment : Set.Icc t0 t ⊆ Set.Ioo (t0 - ε) (t0 + ε) ∩ I := by
      intro r hr
      exact ⟨⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩, hI.out ht0 htI hr⟩
    have hd := fun r (hr : r ∈ Set.Icc t0 t) ↦ hdata (hsegment hr)
    exact ODE_solution_unique_of_mem_Icc_right (fun r _ ↦ hLip r)
      (fun r hr ↦ (hd r hr).1.2.continuousAt.continuousWithinAt)
      (fun r hr ↦ (hd r (Set.Ico_subset_Icc_self hr)).1.2.hasDerivWithinAt)
      (fun r hr ↦ (hd r (Set.Ico_subset_Icc_self hr)).2.2.1)
      (fun r hr ↦ (hd r hr).2.1.2.continuousAt.continuousWithinAt)
      (fun r hr ↦ (hd r (Set.Ico_subset_Icc_self hr)).2.1.2.hasDerivWithinAt)
      (fun r hr ↦ (hd r (Set.Ico_subset_Icc_self hr)).2.2.2)
      heq ⟨horder, le_rfl⟩
  · have hle : t ≤ t0 := (lt_of_not_ge horder).le
    have hsegment : Set.Icc t t0 ⊆ Set.Ioo (t0 - ε) (t0 + ε) ∩ I := by
      intro r hr
      exact ⟨⟨ht.1.trans_le hr.1, by linarith [hr.2]⟩, hI.out htI ht0 hr⟩
    have hd := fun r (hr : r ∈ Set.Icc t t0) ↦ hdata (hsegment hr)
    exact ODE_solution_unique_of_mem_Icc_left (fun r _ ↦ hLip r)
      (fun r hr ↦ (hd r hr).1.2.continuousAt.continuousWithinAt)
      (fun r hr ↦ (hd r (Set.Ioc_subset_Icc_self hr)).1.2.hasDerivWithinAt)
      (fun r hr ↦ (hd r (Set.Ioc_subset_Icc_self hr)).2.2.1)
      (fun r hr ↦ (hd r hr).2.1.2.continuousAt.continuousWithinAt)
      (fun r hr ↦ (hd r (Set.Ioc_subset_Icc_self hr)).2.1.2.hasDerivWithinAt)
      (fun r hr ↦ (hd r (Set.Ioc_subset_Icc_self hr)).2.2.2)
      heq ⟨le_rfl, hle⟩

theorem openODE_eqOn_preconnected (S : Set (ℝ × E)) (hS : IsOpen S)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ 1 V S)
    (I : Set ℝ) (hI : IsPreconnected I) (f g : ℝ → E)
    (hfc : ContinuousOn f I) (hgc : ContinuousOn g I)
    (t0 : ℝ) (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ t ∈ I, (t, f t) ∈ S ∧ HasDerivAt f (V (t, f t)) t)
    (hg : ∀ t ∈ I, (t, g t) ∈ S ∧ HasDerivAt g (V (t, g t)) t) :
    Set.EqOn f g I := by
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
  let A : Set I := {t | f t = g t}
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal := openODE_eventuallyEqWithin S hS V hV I hI.ordConnected f g
      t t.property (hf t t.property).1 ht (hfc t t.property) (hgc t t.property)
      (eventually_nhdsWithin_of_forall hf) (eventually_nhdsWithin_of_forall hg)
    exact (eventually_nhds_subtype_iff I t (fun r ↦ f r = g r)).mpr hlocal
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t0, ht0⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ A := by rw [hAll]; trivial
  exact hm

end PoincareConjecture.Proofs.M09
