import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.ParametricInverse










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace Poincare.Manifold.Schoenflies.Plane



theorem surjective_of_add_period {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : ∀ t, f (t + T) = f t + T) : Surjective f := by
  have hnat (n : ℕ) (t : ℝ) : f (t + (n : ℝ) * T) = f t + (n : ℝ) * T := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hper, ih]
      ring
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt ((|y - f 0| + 1) / T)
  have hB : |y - f 0| + 1 < (N : ℝ) * T := (div_lt_iff₀ hT).mp hN
  have hplus : f ((N : ℝ) * T) = f 0 + (N : ℝ) * T := by simpa using hnat N 0
  have hminus : f (-((N : ℝ) * T)) = f 0 - (N : ℝ) * T := by
    have h := hnat N (-((N : ℝ) * T))
    rw [neg_add_cancel] at h
    linarith
  exact intermediate_value_univ (-((N : ℝ) * T)) ((N : ℝ) * T) hf
    ⟨by rw [hminus]; linarith [neg_abs_le (y - f 0)],
      by rw [hplus]; linarith [le_abs_self (y - f 0)]⟩



theorem exists_smooth_inverse_of_add_period
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : V × ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hF : ContDiff ℝ ∞ F)
    (hper : ∀ z t, F (z, t + T) = F (z, t) + T)
    (hpos : ∀ z t, 0 < deriv (fun s => F (z, s)) t) :
    ∃ G : V × ℝ → ℝ, ContDiff ℝ ∞ G ∧ ∀ z t,
      F (z, G (z, t)) = t ∧ G (z, F (z, t)) = t ∧
        G (z, t + T) = G (z, t) + T := by
  have hsurj (z : V) : Surjective (fun t => F (z, t)) :=
    surjective_of_add_period hT
      (hF.continuous.comp (continuous_const.prodMk continuous_id)) (hper z)
  let D := fiberDiffeomorph hF hpos hsurj
  let G : V × ℝ → ℝ := fun p => (D.symm p).2
  have hfst (p : V × ℝ) : (D.symm p).1 = p.1 := by
    have h := congrArg Prod.fst (D.apply_symm_apply p)
    simpa only [D, fiberDiffeomorph_apply] using h
  have hleft (z : V) (t : ℝ) : F (z, G (z, t)) = t := by
    have h := congrArg Prod.snd (D.apply_symm_apply (z, t))
    change F ((D.symm (z, t)).1, G (z, t)) = t at h
    rwa [hfst] at h
  have hright (z : V) (t : ℝ) : G (z, F (z, t)) = t :=
    congrArg Prod.snd (D.symm_apply_apply (z, t))
  refine ⟨G, D.symm.contDiff.snd, ?_⟩
  intro z t
  refine ⟨hleft z t, hright z t, ?_⟩
  apply (strictMono_of_deriv_pos (hpos z)).injective
  change F (z, G (z, t + T)) = F (z, G (z, t) + T)
  rw [hleft, hper, hleft]

end Poincare.Manifold.Schoenflies.Plane
