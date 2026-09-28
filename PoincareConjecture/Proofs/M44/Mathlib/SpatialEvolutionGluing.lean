import PoincareConjecture.Proofs.M44.Mathlib.TimeJetGluing
import PoincareConjecture.Proofs.M44.Mathlib.CompactTimeLimit
import PoincareConjecture.Proofs.M44.Mathlib.SpatialJetsWithin
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Prolongation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds.Bootstrap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]





theorem contDiffOn_of_spatial_evolution_off_finite
    {J S : Set ℝ} {U : Set E} (hJ : IsOpen J) (hU : IsOpen U) (hS : S.Finite)
    {n : ℕ} {Q : Jet E V n → V} {Omega : Set (Jet E V n)}
    (hOmega : IsOpen Omega) (hQ : ContDiffOn ℝ ∞ Q Omega)
    {f : ℝ × E → V}
    (hsmooth : ContDiffOn ℝ ∞ f ((J \ S) ×ˢ U))
    (hspace : ∀ t ∈ J, ContDiffOn ℝ ∞ (fun x => f (t, x)) U)
    (hjets : ∀ m : ℕ, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ m (fun x => f (p.1, x)) p.2) (J ×ˢ U))
    (hrange : ∀ p ∈ J ×ˢ U, spatialJet n f p ∈ Omega)
    (hevol : ∀ t ∈ J, t ∉ S → ∀ x ∈ U,
      HasDerivAt (fun s => f (s, x)) (Q (spatialJet n f (t, x))) t) :
    ContDiffOn ℝ ∞ f (J ×ˢ U) := by
  let A (m : ℕ) (p : ℝ × E) := iteratedFDeriv ℝ m (fun x => f (p.1, x)) p.2
  let D (m : ℕ) : (E [×(m + 1)]→L[ℝ] V) →L[ℝ] E →L[ℝ] E [×m]→L[ℝ] V :=
    (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => E) V).toContinuousLinearEquiv.toContinuousLinearMap
  have hregular : IsOpen (J \ S) := hJ.sdiff hS.isClosed
  have hfields : ∀ m, ContDiffOn ℝ ∞ (A m) (J ×ˢ U) := by
    apply Poincare.contDiffOn_of_finite_jet_evolution hJ hU hS A D
      (fun m => n + m + 1) (operator n Q)
      (fun m => (baseProjection n m) ⁻¹' Omega)
      (fun m => contDiffOn_operator hOmega hQ m)
    · intro m p hp
      change baseProjection n m (spatialJet (n + m) f p) ∈ Omega
      simpa only [baseProjection_spatialJet] using hrange p hp
    · exact hjets
    · intro m t ht x hx
      have hg := (hspace t ht).contDiffAt (hU.mem_nhds hx)
      have hd := (hg.iteratedFDeriv_right (i := m) (m := 1)
        (by exact_mod_cast le_top)).differentiableAt (by simp) |>.hasFDerivAt
      change HasFDerivAt (iteratedFDeriv ℝ m (fun y => f (t, y)))
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V)
          (iteratedFDeriv ℝ (m + 1) (fun y => f (t, y)) x)) x
      rw [iteratedFDeriv_succ_eq_comp_left]
      simpa only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using hd
    · intro m t ht hnot x hx
      change HasDerivAt (fun s => iteratedFDeriv ℝ m (fun y => f (s, y)) x)
        (operator n Q m (spatialJet (n + m) f (t, x))) t
      rw [operator_spatialJet hOmega hQ hsmooth hregular hU
        (fun p hp => hrange p ⟨hp.1.1, hp.2⟩) ⟨ht, hnot⟩ hx m]
      exact SpacetimeBounds.hasDerivAt_spatialJet hsmooth hregular hU ⟨ht, hnot⟩
        (hevol t ht hnot) m hx
  exact (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hfields 0)




theorem continuousOn_spatialJets_of_compact_uniform
    [ProperSpace E] {f : ℝ × E → V} {U : Set E} {a T b : ℝ}
    (hU : IsOpen U) (hTb : T < b)
    (hleft : ContDiffOn ℝ ∞ f (Ioo a T ×ˢ U))
    (hright : ContDiffOn ℝ ∞ f (Ico T b ×ˢ U))
    (hlim : ∀ m : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧
        ∀ t : ℝ, T - d < t → t < T → ∀ x ∈ K,
          ‖iteratedFDeriv ℝ m (fun y => f (t, y)) x -
            iteratedFDeriv ℝ m (fun y => f (T, y)) x‖ < eta) :
    ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => f (p.1, x)) p.2) (Ioo a b ×ˢ U) := by
  intro m
  apply Poincare.continuousOn_time_of_compact_uniform hU hTb
    (contDiffOn_spatialJet_within hleft isOpen_Ioo.uniqueDiffOn hU m).continuousOn
    (contDiffOn_spatialJet_within hright (uniqueDiffOn_Ico T b) hU m).continuousOn
  simpa only [dist_eq_norm] using hlim m

end PoincareConjecture.M44
