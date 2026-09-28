import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarEnergyPositive
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.FromEmbedding













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)






theorem scalarAnnulusDefining_nonneg (x : Plane) :
    0 ≤ scalarAnnulusDefining x ↔ 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  have hn := norm_nonneg x
  change 0 ≤ (‖x‖ ^ 2 - 1) * (4 - ‖x‖ ^ 2) ↔ 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2
  constructor
  · intro h
    rcases mul_nonneg_iff.mp h with h | h <;> constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    apply mul_nonneg <;> nlinarith






theorem scalarAnnulusDefining_zero (x : Plane) :
    scalarAnnulusDefining x = 0 ↔ ‖x‖ = 1 ∨ ‖x‖ = 2 := by
  have hn := norm_nonneg x
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  · rintro (h | h) <;> norm_num [scalarAnnulusDefining, h]






theorem scalarAnnulusDefining_regular_zero (x : Plane)
    (hx : scalarAnnulusDefining x = 0) :
    Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) scalarAnnulusDefining x) :=
  scalarAnnulusDefining_regular ((scalarAnnulusDefining_zero x).mp hx)






theorem scalarClosedAnnulus_isCompact :
    IsCompact {x : Plane | 0 ≤ scalarAnnulusDefining x} := by
  apply (isCompact_closedBall (0 : Plane) 2).of_isClosed_subset
    (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    ((scalarAnnulusDefining_nonneg x).mp hx).2






theorem scalarClosedAnnulus_isConnected :
    IsConnected {x : Plane | 0 ≤ scalarAnnulusDefining x} := by
  have hs : IsConnected (Metric.sphere (0 : Plane) 1) :=
    isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one
  have hi : IsConnected (Icc (1 : ℝ) 2) := isConnected_Icc (by norm_num)
  have himage := (hs.prod hi).image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have heq : {x : Plane | 0 ≤ scalarAnnulusDefining x} =
      (fun p : Plane × ℝ => p.2 • p.1) ''
        (Metric.sphere (0 : Plane) 1 ×ˢ Icc (1 : ℝ) 2) := by
    ext x
    simp only [mem_ofPred_eq, scalarAnnulusDefining_nonneg, mem_image, mem_prod,
      mem_Icc, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx.1
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_norm, inv_mul_cancel₀ hxpos.ne']
      · rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs,
        abs_of_pos (lt_of_lt_of_le zero_lt_one ht.1)]
      exact ht
  rw [heq]
  exact himage






theorem scalarClosedAnnulus_interior :
    interior {x : Plane | 0 ≤ scalarAnnulusDefining x} = scalarAnnulus := by
  rw [← self_sdiff_frontier, Poincare.Manifold.frontier_superlevel_eq_regular_level
    scalarAnnulusDefining_smooth 0 scalarAnnulusDefining_regular_zero]
  ext x
  change (0 ≤ scalarAnnulusDefining x ∧ ¬ scalarAnnulusDefining x = 0) ↔ _
  rw [← scalarAnnulusDefining_pos]
  exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩







theorem nonempty_scalarAnnulus_smoothDomain :
    Nonempty (Poincare.Manifold.SmoothDomain 2 scalarAnnulus) := by
  obtain ⟨K, CS, _, _, hK, _, hman, hemb⟩ :=
    Poincare.Manifold.exists_regular_superlevel_smooth_embedding
      (n := 1) (by simp : Module.finrank ℝ Plane = 1 + 1)
      scalarAnnulusDefining_smooth 0 scalarAnnulusDefining_regular_zero
  let := CS
  let := hman
  have hcompact : IsCompact K := by
    rw [hK]
    exact scalarClosedAnnulus_isCompact
  have hconnected : IsConnected K := by
    rw [hK]
    exact scalarClosedAnnulus_isConnected
  have hinterior : interior K = scalarAnnulus := by
    rw [hK]
    exact scalarClosedAnnulus_interior
  simpa only [hinterior] using
    Poincare.Manifold.nonempty_smoothDomain_interior hcompact hconnected hemb

end PoincareConjecture.M64Uniformization
