import PoincareConjecture.Proofs.M35.RadialGauge.ForcingJetAlgebra
import PoincareConjecture.Proofs.M35.RadialGauge.RadialExteriorJets
import PoincareConjecture.Proofs.M35.RadialGauge.ScalarWeightedProducts
import Mathlib.Analysis.Normed.Operator.Prod











set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {A E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exterior_joint_profile_jets {f : A → ℝ → ℝ} {N : ℕ}
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (f a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ p : E × ℝ, 1 ≤ ‖p.1‖ →
      (1 + ‖p.1‖) ^ N * ‖iteratedFDeriv ℝ j (fun q : E × ℝ => f a ‖q.1‖) p‖ ≤ C := by
  have hV : IsOpen (({0} : Set E)ᶜ) := isClosed_singleton.isOpen_compl
  have hn : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) ({0} : Set E)ᶜ :=
    fun x hx => (contDiffAt_id.norm ℝ (show x ≠ 0 from hx)).contDiffWithinAt
  have hs (a : A) : ContDiffOn ℝ ∞ (fun x : E => f a ‖x‖) ({0} : Set E)ᶜ :=
    (hf a).comp hn (fun x hx => norm_pos_iff.mpr hx)
  intro j
  obtain ⟨C, hC, hCb⟩ := radial_exterior_weighted_jets (E := E) hf hb j
  refine ⟨C, hC, ?_⟩
  intro a p hp
  have hx : p.1 ∈ ({0} : Set E)ᶜ := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hp)
  have h := norm_jet_comp_linear_le (ContinuousLinearMap.fst ℝ E ℝ)
    (ContinuousLinearMap.norm_fst_le ℝ E ℝ) hV (hs a) hx j
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (hCb a p.1 hp)




theorem exterior_forcing_formula_jets
    {c invf : A → ℝ → ℝ} {target : E × ℝ → ℝ} {eta : ℝ}
    (hc : ∀ a, ContDiffOn ℝ ∞ (c a) (Ioi 0))
    (hi : ∀ a, ContDiffOn ℝ ∞ (invf a) (Ioi 0))
    (hcb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) * |iteratedDeriv j (c a) r| ≤ C)
    (hib : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (invf a) r| ≤ C)
    (hT : ContDiff ℝ ∞ target)
    (hTb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |p.2| ≤ eta →
      (1 + ‖p.1‖) * ‖iteratedFDeriv ℝ j target p‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E, ∀ sigma,
      1 ≤ ‖x‖ → |sigma| ≤ eta →
      (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (fun p : E × ℝ =>
        c a ‖p.1‖ + 2 / ‖p.1‖ ^ 2 - 2 * target p * invf a ‖p.1‖ ^ 2) (x, sigma)‖ ≤ C := by
  let U : Set (E × ℝ) := {p | p.1 ≠ 0}
  let S : Set (E × ℝ) := {p | 1 ≤ ‖p.1‖ ∧ |p.2| ≤ eta}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage continuous_fst
  have hS : S ⊆ U := fun p hp => norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hp.1)
  have hw (p : E × ℝ) (_hp : p ∈ S) : 0 ≤ 1 + ‖p.1‖ := by positivity
  have hn : ContDiffOn ℝ ∞ (fun p : E × ℝ => ‖p.1‖) U :=
    fun p hp => (contDiffAt_fst.norm ℝ hp).contDiffWithinAt
  have hs {f : A → ℝ → ℝ} (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0)) (a : A) :
      ContDiffOn ℝ ∞ (fun p : E × ℝ => f a ‖p.1‖) U :=
    (hf a).comp hn (fun p hp => norm_pos_iff.mpr hp)
  have hb {f : A → ℝ → ℝ} (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
      (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
        |iteratedDeriv j (f a) r| ≤ C) :
      ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a p, p ∈ S →
        ‖iteratedFDeriv ℝ j (fun q : E × ℝ => f a ‖q.1‖) p‖ ≤ C := by
    intro j
    have hweight (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
        (1 + r) ^ (0 : ℕ) * |iteratedDeriv i (f a) r| ≤ C := by
      simpa only [pow_zero, one_mul] using hfb i
    obtain ⟨C, hC, hCb⟩ := exterior_joint_profile_jets (E := E) hf hweight j
    simp only [pow_zero, one_mul] at hCb
    exact ⟨C, hC, fun a p hp => hCb a p hp.1⟩
  have hbw {f : A → ℝ → ℝ} (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
      (hfb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
        (1 + r) * |iteratedDeriv j (f a) r| ≤ C) :
      ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a p, p ∈ S →
        (1 + ‖p.1‖) * ‖iteratedFDeriv ℝ j (fun q : E × ℝ => f a ‖q.1‖) p‖ ≤ C := by
    intro j
    have hweight (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
        (1 + r) ^ (1 : ℕ) * |iteratedDeriv i (f a) r| ≤ C := by
      simpa only [pow_one] using hfb i
    obtain ⟨C, hC, hCb⟩ := exterior_joint_profile_jets (E := E) hf hweight j
    simp only [pow_one] at hCb
    exact ⟨C, hC, fun a p hp => hCb a p hp.1⟩
  have hir (a : A) : ContDiffOn ℝ ∞ (fun r : ℝ => 1 / r) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun _ hr => ne_of_gt hr)
  have hirb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (_a : A) r, 1 ≤ r →
      |iteratedDeriv j (fun s : ℝ => 1 / s) r| ≤ C :=
    ⟨j.factorial, Nat.cast_nonneg _, fun _ _ hr => reciprocal_radius_jet_bound j hr⟩
  have hirw (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (_a : A) r, 1 ≤ r →
      (1 + r) * |iteratedDeriv j (fun s : ℝ => 1 / s) r| ≤ C :=
    ⟨2 * j.factorial, by positivity,
      fun _ _ hr => reciprocal_radius_weighted_jet_bound j hr⟩
  have hirs := hs hir
  have hsq := family_weighted_jet_bounds_mul hU hS hw hirs hirs
    (hbw hir hirw) (hb hir hirb)
  have hneg := family_weighted_jet_bounds_const_mul hU hS
    (fun a => (hirs a).mul (hirs a)) hsq (-2)
  have hfirst := family_weighted_jet_bounds_sub hU hS hw (hs hc)
    (fun a => contDiffOn_const.mul ((hirs a).mul (hirs a))) (hbw hc hcb) hneg
  have htargetb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (_a : A) p, p ∈ S →
      (1 + ‖p.1‖) * ‖iteratedFDeriv ℝ j target p‖ ≤ C := by
    obtain ⟨C, hC, hCb⟩ := hTb j
    exact ⟨C, hC, fun _ p hp => hCb p hp.2⟩
  have hinvsq := family_jet_bounds_mul hU hS (hs hi) (hs hi) (hb hi hib) (hb hi hib)
  have htarget := family_weighted_jet_bounds_mul hU hS hw (fun _ => hT.contDiffOn)
    (fun a => (hs hi a).mul (hs hi a)) htargetb hinvsq
  have htwotarget := family_weighted_jet_bounds_const_mul hU hS
    (fun a => hT.contDiffOn.mul ((hs hi a).mul (hs hi a))) htarget 2
  have hfull := family_weighted_jet_bounds_sub hU hS hw
    (fun a => (hs hc a).sub (contDiffOn_const.mul ((hirs a).mul (hirs a))))
    (fun a => contDiffOn_const.mul (hT.contDiffOn.mul ((hs hi a).mul (hs hi a))))
    hfirst htwotarget
  intro j
  obtain ⟨C, hC, hCb⟩ := hfull j
  refine ⟨C, hC, ?_⟩
  intro a x sigma hx hsigma
  have heq : (fun p : E × ℝ => c a ‖p.1‖ + 2 / ‖p.1‖ ^ 2 -
      2 * target p * invf a ‖p.1‖ ^ 2) =
      (fun p : E × ℝ => (c a ‖p.1‖ - -2 * ((1 / ‖p.1‖) * (1 / ‖p.1‖))) -
        2 * (target p * (invf a ‖p.1‖ * invf a ‖p.1‖))) := by
    funext p
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  exact hCb a (x, sigma) ⟨hx, hsigma⟩

end PoincareConjecture.M35.RadialGauge
