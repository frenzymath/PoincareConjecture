import PoincareConjecture.Proofs.M34.Standard.InitialJetDerivative
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
  (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
  {f : ℝ × E → V} {T : ℝ}
  (hf : ContDiffOn ℝ ∞ f (Ioo 0 T ×ˢ univ))
  (hc : ∀ j, ContinuousOn
    (fun p : ℝ × E => iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2)
    (Ico 0 T ×ˢ univ))
  (hrange : ∀ p ∈ Ico 0 T ×ˢ univ, spatialJet n f p ∈ Ω)
  (hevol : ∀ p ∈ Ioo 0 T ×ˢ univ,
    deriv (fun t => f (t, p.2)) p.1 = Q (spatialJet n f p))

include hΩ hQ hf hc hrange hevol



theorem contDiffOn_spatialJets_of_initial_evolution (j : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2)
      (Ico 0 T ×ˢ univ) := by
  have hfinite : ∀ r : ℕ, ∀ k, ContDiffOn ℝ r
      (fun p : ℝ × E => iteratedFDeriv ℝ k (fun x => f (p.1, x)) p.2)
      (Ico 0 T ×ˢ univ) := by
    intro r
    induction r with
    | zero => exact fun k => contDiffOn_zero.mpr (hc k)
    | succ r ih =>
      intro k
      change ContDiffOn ℝ ((r : ℕ∞ω) + 1) _ _
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        ((uniqueDiffOn_Ico 0 T).prod uniqueDiffOn_univ)).mpr
      refine ⟨by simp, initialJointJetDerivative n Q f k, ?_, ?_⟩
      · exact contDiffOn_initialJointJetDerivative hΩ hQ
          (by exact_mod_cast le_top) ih hrange k
      · intro p hp
        exact hasFDerivWithinAt_initialJointJetDerivative hΩ hQ hf hc hrange hevol k hp
  exact contDiffOn_infty.mpr (fun r => hfinite r j)




theorem contDiffOn_of_initial_spatial_jet_evolution :
    ContDiffOn ℝ ∞ f (Ico 0 T ×ˢ univ) := by
  have hzero := contDiffOn_spatialJets_of_initial_evolution hΩ hQ hf hc hrange hevol 0
  exact (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    hzero



theorem hasDerivWithinAt_of_initial_spatial_jet_evolution
    {p : ℝ × E} (hp : p ∈ Ico 0 T ×ˢ univ) :
    HasDerivWithinAt (fun t => f (t, p.2)) (Q (spatialJet n f p)) (Ico 0 T) p.1 := by
  have hd := hasFDerivWithinAt_initialJointJetDerivative hΩ hQ hf hc hrange hevol 0 hp
  have hpath : HasDerivWithinAt (fun t : ℝ => (t, p.2)) (1, 0) (Ico 0 T) p.1 :=
    (hasDerivWithinAt_id p.1 (Ico 0 T)).prodMk
      (hasDerivWithinAt_const p.1 (Ico 0 T) p.2)
  have hmap : MapsTo (fun t : ℝ => (t, p.2)) (Ico 0 T) (Ico 0 T ×ˢ univ) :=
    fun _ ht => ⟨ht, mem_univ p.2⟩
  have ht := hd.comp_hasDerivWithinAt p.1 hpath hmap
  let L : (E [×0]→L[ℝ] V) →L[ℝ] V :=
    (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivWithinAt p.1 ht
  convert! h using 1
  simp [L, initialJointJetDerivative, timeLift, spaceLift, operator]

end PoincareConjecture.M34
