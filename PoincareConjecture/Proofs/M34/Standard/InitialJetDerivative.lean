import PoincareConjecture.Proofs.M34.Mathlib.InitialDerivativeExtension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]



noncomputable def initialJointJetDerivative (n : ℕ) (Q : Jet E V n → V)
    (f : ℝ × E → V) (j : ℕ) (p : ℝ × E) :
    ℝ × E →L[ℝ] E [×j]→L[ℝ] V :=
  timeLift (E := E) (operator n Q j (spatialJet (n + j) f p)) +
    spaceLift ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V)
      (iteratedFDeriv ℝ (j + 1) (fun x => f (p.1, x)) p.2))



theorem contDiffOn_initialJointJetDerivative
    {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {f : ℝ × E → V} {S : Set (ℝ × E)} {r : ℕ∞ω} (hr : r ≤ ∞)
    (hjets : ∀ j, ContDiffOn ℝ r
      (fun p : ℝ × E => iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2) S)
    (hrange : ∀ p ∈ S, spatialJet n f p ∈ Ω) (j : ℕ) :
    ContDiffOn ℝ r (initialJointJetDerivative n Q f j) S := by
  have hfinite : ContDiffOn ℝ r (spatialJet (n + j) f) S :=
    contDiffOn_pi.mpr (fun k => hjets k)
  have htime : ContDiffOn ℝ r
      (fun p => operator n Q j (spatialJet (n + j) f p)) S := by
    apply ((contDiffOn_operator hΩ hQ j).of_le hr).comp hfinite
    intro p hp
    simpa only [mem_preimage, baseProjection_spatialJet] using hrange p hp
  have hcurry : ContDiff ℝ r
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V) := by
    fun_prop
  exact ((timeLift (E := E) (V := E [×j]→L[ℝ] V)).contDiff.comp_contDiffOn htime).add
    ((spaceLift (E := E) (V := E [×j]→L[ℝ] V)).contDiff.comp_contDiffOn
      (hcurry.comp_contDiffOn (hjets (j + 1))))



theorem hasFDerivAt_initialJointJetDerivative
    {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {f : ℝ × E → V} {T : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 T ×ˢ univ))
    (hrange : ∀ p ∈ Ioo 0 T ×ˢ univ, spatialJet n f p ∈ Ω)
    (hevol : ∀ p ∈ Ioo 0 T ×ˢ univ,
      deriv (fun t => f (t, p.2)) p.1 = Q (spatialJet n f p))
    (j : ℕ) {p : ℝ × E} (hp : p ∈ Ioo 0 T ×ˢ univ) :
    HasFDerivAt (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2)
      (initialJointJetDerivative n Q f j p) p := by
  have hd := ((SpacetimeBounds.contDiffOn_spatialJet hf isOpen_Ioo isOpen_univ j).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have heq : fderiv ℝ
      (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2) p =
      initialJointJetDerivative n Q f j p := by
    rw [fderiv_eq_partials hd]
    rw [deriv_spatialJet_eq_operator hΩ hQ hf isOpen_Ioo isOpen_univ
      hrange hevol j hp]
    rfl
  simpa only [heq] using hd.hasFDerivAt



theorem hasFDerivWithinAt_initialJointJetDerivative
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
    (j : ℕ) {p : ℝ × E} (hp : p ∈ Ico 0 T ×ˢ univ) :
    HasFDerivWithinAt
      (fun z : ℝ × E => iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2)
      (initialJointJetDerivative n Q f j p) (Ico 0 T ×ˢ univ) p := by
  apply hasFDerivWithinAt_Ico_prod_of_continuousOn (hc j) _ _ hp
  · exact (contDiffOn_initialJointJetDerivative hΩ hQ (r := 0) (by simp)
      (fun k => contDiffOn_zero.mpr (hc k)) hrange j).continuousOn
  · intro z hz
    exact hasFDerivAt_initialJointJetDerivative hΩ hQ hf
      (fun w hw => hrange w ⟨Ioo_subset_Ico_self hw.1, hw.2⟩) hevol j hz

end PoincareConjecture.M34
