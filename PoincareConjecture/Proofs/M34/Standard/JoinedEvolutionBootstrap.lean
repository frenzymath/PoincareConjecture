import PoincareConjecture.Proofs.M34.Mathlib.DerivativeJoining
import PoincareConjecture.Proofs.M34.Standard.InitialJetDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasFDerivAt_jointJetDerivative_of_open
    {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {f : ℝ × E → V} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hrange : ∀ p ∈ U ×ˢ univ, spatialJet n f p ∈ Ω)
    (hevol : ∀ p ∈ U ×ˢ univ,
      deriv (fun t => f (t, p.2)) p.1 = Q (spatialJet n f p))
    (j : ℕ) {p : ℝ × E} (hp : p ∈ U ×ˢ univ) :
    HasFDerivAt (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2)
      (initialJointJetDerivative n Q f j p) p := by
  have hd := ((SpacetimeBounds.contDiffOn_spatialJet hf hU isOpen_univ j).contDiffAt
    ((hU.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have heq : fderiv ℝ
      (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2) p =
      initialJointJetDerivative n Q f j p := by
    rw [fderiv_eq_partials hd]
    rw [deriv_spatialJet_eq_operator hΩ hQ hf hU isOpen_univ hrange hevol j hp]
    rfl
  simpa only [heq] using hd.hasFDerivAt

variable {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
  (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
  {f : ℝ × E → V} {a b c : ℝ}
  (hf : ContDiffOn ℝ ∞ f ((Ioo a b \ {c}) ×ˢ univ))
  (hc : ∀ j, ContinuousOn
    (fun p : ℝ × E => iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2)
    (Ioo a b ×ˢ univ))
  (hrange : ∀ p ∈ Ioo a b ×ˢ univ, spatialJet n f p ∈ Ω)
  (hevol : ∀ p ∈ (Ioo a b \ {c}) ×ˢ univ,
    deriv (fun t => f (t, p.2)) p.1 = Q (spatialJet n f p))

include hΩ hQ hf hc hrange hevol

theorem hasFDerivAt_joinedJointJetDerivative (j : ℕ) {p : ℝ × E}
    (hp : p ∈ Ioo a b ×ˢ univ) :
    HasFDerivAt (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2)
      (initialJointJetDerivative n Q f j p) p := by
  apply hasFDerivAt_prod_of_continuousOn_off_time (c := c) (hc j) _ _ hp
  · exact (contDiffOn_initialJointJetDerivative hΩ hQ (r := 0) (by simp)
      (fun k => contDiffOn_zero.mpr (hc k)) hrange j).continuousOn
  · intro q hq hqc
    apply hasFDerivAt_jointJetDerivative_of_open hΩ hQ
      (isOpen_Ioo.sdiff isClosed_singleton) hf
      (fun z hz => hrange z ⟨hz.1.1, hz.2⟩) hevol j
    exact ⟨⟨hq.1, hqc⟩, hq.2⟩

theorem contDiffOn_spatialJets_of_joined_evolution (j : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2)
      (Ioo a b ×ˢ univ) := by
  have hfinite : ∀ r : ℕ, ∀ k, ContDiffOn ℝ r
      (fun p : ℝ × E => iteratedFDeriv ℝ k (fun x => f (p.1, x)) p.2)
      (Ioo a b ×ˢ univ) := by
    intro r
    induction r with
    | zero => exact fun k => contDiffOn_zero.mpr (hc k)
    | succ r ih =>
      intro k
      change ContDiffOn ℝ ((r : ℕ∞ω) + 1) _ _
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        (isOpen_Ioo.prod isOpen_univ).uniqueDiffOn).mpr
      refine ⟨by simp, initialJointJetDerivative n Q f k, ?_, ?_⟩
      · exact contDiffOn_initialJointJetDerivative hΩ hQ
          (by exact_mod_cast le_top) ih hrange k
      · intro p hp
        have hd := hasFDerivAt_joinedJointJetDerivative hΩ hQ hf hc hrange hevol k hp
        exact hd.hasFDerivWithinAt
  exact contDiffOn_infty.mpr (fun r => hfinite r j)

theorem contDiffOn_of_joined_spatial_jet_evolution :
    ContDiffOn ℝ ∞ f (Ioo a b ×ˢ univ) := by
  have hz := contDiffOn_spatialJets_of_joined_evolution hΩ hQ hf hc hrange hevol 0
  exact (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.contDiff.comp_contDiffOn hz

theorem hasDerivAt_of_joined_spatial_jet_evolution
    {p : ℝ × E} (hp : p ∈ Ioo a b ×ˢ univ) :
    HasDerivAt (fun t => f (t, p.2)) (Q (spatialJet n f p)) p.1 := by
  have hd := hasFDerivAt_joinedJointJetDerivative hΩ hQ hf hc hrange hevol 0 hp
  have hpath : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have ht := hd.comp_hasDerivAt p.1 hpath
  let L : (E [×0]→L[ℝ] V) →L[ℝ] V :=
    (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivAt p.1 ht
  convert! h using 1
  simp [L, initialJointJetDerivative, timeLift, spaceLift, operator]

end PoincareConjecture.M34
