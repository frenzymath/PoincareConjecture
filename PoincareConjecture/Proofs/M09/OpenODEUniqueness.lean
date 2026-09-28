import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open scoped Topology

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem openODE_eventuallyEq (S : Set (ℝ × E)) (hS : IsOpen S)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ 1 V S)
    (f g : ℝ → E) (t0 : ℝ) (h0 : (t0, f t0) ∈ S) (heq : f t0 = g t0)
    (hf : ∀ᶠ t in 𝓝 t0, (t, f t) ∈ S ∧ HasDerivAt f (V (t, f t)) t)
    (hg : ∀ᶠ t in 𝓝 t0, (t, g t) ∈ S ∧ HasDerivAt g (V (t, g t)) t) :
    f =ᶠ[𝓝 t0] g := by
  obtain ⟨K, Q, hQ, hL⟩ := (hV.contDiffAt (hS.mem_nhds h0)).exists_lipschitzOnWith
  have hLip : ∀ t : ℝ, LipschitzOnWith K (fun x ↦ V (t, x)) {x | (t, x) ∈ Q} := by
    intro t x hx y hy
    simpa only [Prod.edist_eq, edist_self,
      max_eq_right (show 0 ≤ edist x y from bot_le)] using hL hx hy
  have hfQ : ∀ᶠ t in 𝓝 t0, (t, f t) ∈ Q :=
    (continuousAt_id.prodMk hf.self_of_nhds.2.continuousAt).preimage_mem_nhds hQ
  have hgQ : ∀ᶠ t in 𝓝 t0, (t, g t) ∈ Q := by
    apply (continuousAt_id.prodMk hg.self_of_nhds.2.continuousAt).preimage_mem_nhds
    simpa only [heq, Function.id_def] using hQ
  exact ODE_solution_unique_of_eventually (Filter.Eventually.of_forall hLip)
    ((hf.and hfQ).mono (fun _ h ↦ ⟨h.1.2, h.2⟩))
    ((hg.and hgQ).mono (fun _ h ↦ ⟨h.1.2, h.2⟩)) heq

theorem openODE_eqOn (S : Set (ℝ × E)) (hS : IsOpen S)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ 1 V S)
    (I : Set ℝ) (hI : IsOpen I) (hconn : IsPreconnected I)
    (f g : ℝ → E) (t0 : ℝ) (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ t ∈ I, (t, f t) ∈ S ∧ HasDerivAt f (V (t, f t)) t)
    (hg : ∀ t ∈ I, (t, g t) ∈ S ∧ HasDerivAt g (V (t, g t)) t) :
    Set.EqOn f g I := by
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hconn
  let A : Set I := {t | f t = g t}
  have hfc : ContinuousOn f I := fun t ht ↦ (hf t ht).2.continuousAt.continuousWithinAt
  have hgc : ContinuousOn g I := fun t ht ↦ (hg t ht).2.continuousAt.continuousWithinAt
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hf' : ∀ᶠ r in 𝓝 (t : ℝ),
        (r, f r) ∈ S ∧ HasDerivAt f (V (r, f r)) r :=
      Filter.Eventually.mono (hI.mem_nhds t.property) (fun r hr ↦ hf r hr)
    have hg' : ∀ᶠ r in 𝓝 (t : ℝ),
        (r, g r) ∈ S ∧ HasDerivAt g (V (r, g r)) r :=
      Filter.Eventually.mono (hI.mem_nhds t.property) (fun r hr ↦ hg r hr)
    exact continuousAt_subtype_val.preimage_mem_nhds
      (openODE_eventuallyEq S hS V hV f g t (hf t t.property).1 ht hf' hg')
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t0, ht0⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ A := by rw [hAll]; exact Set.mem_univ _
  exact hm

end PoincareConjecture.Proofs.M09
