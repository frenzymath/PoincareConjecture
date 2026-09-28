import PoincareConjecture.Proofs.M47.CanonicalNeckMapJets
import PoincareConjecture.Proofs.M44.Mathlib.CompactTimeModulus









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem metric_jets_uniform_time_delta_on_compact
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {H : Set (EuclideanSpace ℝ (Fin n))} (hH : IsCompact H) (hHU : H ⊆ U)
    (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |s - t| < delta → ∀ x ∈ H, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun y => (F.metric s).pullbackCoefficients e y -
          (F.metric t).pullbackCoefficients e y) x‖ < rho := by
  classical
  have hc (j : Fin (m + 1)) : ContinuousOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        iteratedFDeriv ℝ j.val ((F.metric z.1).pullbackCoefficients e) z.2)
      (Icc a b ×ˢ H) :=
    (M44.continuousOn_pullback_spatialJet hab F hU he j.val).mono
      (fun _ hz => ⟨hz.1, hHU hz.2⟩)
  choose d hd hmod using fun j : Fin (m + 1) =>
    (hc j).exists_uniform_time_delta isCompact_Icc hH hrho
  let delta := Finset.univ.inf' Finset.univ_nonempty d
  have hdelta : 0 < delta := (Finset.lt_inf'_iff _).mpr (fun j _ => hd j)
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst x hx j hj
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hsmall : |s - t| < d i := hst.trans_le (Finset.inf'_le d (Finset.mem_univ i))
  have h := hmod i s hs t ht hsmall x hx
  have he' := he.contMDiffAt (hU.mem_nhds (hHU hx))
  have hnew := (F.metric s).contDiffAt_pullbackCoefficients he'
  have hold := (F.metric t).contDiffAt_pullbackCoefficients he'
  change ‖iteratedFDeriv ℝ j
    ((F.metric s).pullbackCoefficients e - (F.metric t).pullbackCoefficients e) x‖ < rho
  rw [iteratedFDeriv_sub_apply (hnew.of_le (by exact_mod_cast le_top))
    (hold.of_le (by exact_mod_cast le_top))]
  simpa only [dist_eq_norm] using h

end PoincareConjecture.Proofs.M47
