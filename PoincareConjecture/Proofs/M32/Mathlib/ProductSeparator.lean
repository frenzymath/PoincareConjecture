import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture.M32




theorem isCompact_univ_of_separated_product_line
    {X : Type u} {M : Type v} [TopologicalSpace X] [TopologicalSpace M]
    [PathConnectedSpace X] (e : (X × ℝ) ≃ₜ M) (gamma : ℝ → M)
    (hheight : ∀ t : ℝ, (e.symm (gamma t)).2 = t)
    {K : Set M} (hK : IsCompact K) {R₀ : ℝ}
    (hsep : ∀ T : ℝ, R₀ < T → ¬ JoinedIn Kᶜ (gamma (-T)) (gamma T)) :
    IsCompact (univ : Set X) := by
  classical
  by_contra hnoncompact
  let J := e.symm '' K
  have hJ : IsCompact J := hK.image e.symm.continuous
  obtain ⟨q, hq⟩ : ∃ q : X, q ∉ Prod.fst '' J := by
    by_contra h
    push Not at h
    have heq : Prod.fst '' J = univ := eq_univ_of_forall h
    exact hnoncompact (heq ▸ hJ.image continuous_fst)
  obtain ⟨a, ha⟩ := hJ.bddAbove_image (continuous_snd.abs.continuousOn)
  let A := max a 0
  have hA (z : X × ℝ) (hz : z ∈ J) : |z.2| ≤ A :=
    (ha (mem_image_of_mem (fun z : X × ℝ => |z.2|) hz)).trans (le_max_left _ _)
  let T := max R₀ A + 1
  have hTR : R₀ < T := by dsimp [T]; linarith [le_max_left R₀ A]
  have hTA : A < T := by dsimp [T]; linarith [le_max_right R₀ A]
  have hTpos : 0 < T := by dsimp [A] at hTA; linarith [le_max_right a 0]
  have hhorizontal (t : ℝ) (ht : A < |t|) (p q' : X) :
      JoinedIn Jᶜ (p, t) (q', t) := by
    have hpath := (isPathConnected_univ.joinedIn p (mem_univ _) q' (mem_univ _)).map
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => t)))
    apply hpath.mono
    rintro _ ⟨x, _, rfl⟩ hx
    exact not_le_of_gt ht (hA (x, t) hx)
  have hvertical : JoinedIn Jᶜ (q, -T) (q, T) := by
    have hpath := (isPathConnected_univ.joinedIn (-T) (mem_univ _) T (mem_univ _)).map
      ((continuous_const : Continuous (fun _ : ℝ => q)).prodMk continuous_id)
    apply hpath.mono
    rintro _ ⟨t, _, rfl⟩ ht
    exact hq (mem_image_of_mem Prod.fst ht)
  have hpair (t : ℝ) : ((e.symm (gamma t)).1, t) = e.symm (gamma t) := by
    apply Prod.ext
    · rfl
    · exact (hheight t).symm
  have hleft := hhorizontal (-T) (by simpa only [abs_neg, abs_of_pos hTpos] using hTA)
    (e.symm (gamma (-T))).1 q
  have hright := hhorizontal T (by simpa only [abs_of_pos hTpos] using hTA)
    q (e.symm (gamma T)).1
  have hjoined := (hleft.trans hvertical).trans hright
  rw [hpair, hpair] at hjoined
  have hmap := hjoined.map e.continuous
  have houtside : e '' Jᶜ ⊆ Kᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hmem
    exact hz ⟨e z, hmem, e.symm_apply_apply z⟩
  apply hsep T hTR
  simpa only [e.apply_symm_apply] using hmap.mono houtside

end PoincareConjecture.M32
