import PoincareConjecture.Proofs.M35.RadialGauge.RestrictedGaugeJets
import PoincareConjecture.Proofs.M35.RadialGauge.EuclideanGaugeSecondJet

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {m n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))
local notation "W" => EuclideanSpace ℝ (Fin m)

theorem restricted_euclideanGauge_jets_joint_c1 (I : V →L[ℝ] W)
    {u : ℝ → W → ℝ} {J : Set ℝ}
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (u t))
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (J ×ˢ univ))
    (hj : ∀ j : ℕ, ContDiffOn ℝ 1
      (fun p : ℝ × W => iteratedFDeriv ℝ j (u p.1) p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ 1
      (fun p : ℝ × V => euclideanGauge (fun x => u p.1 (I x)) p.2) (J ×ˢ univ) ∧
    ContDiffOn ℝ 1
      (fun p : ℝ × V => fderiv ℝ (euclideanGauge (fun x => u p.1 (I x))) p.2)
      (J ×ˢ univ) ∧
    ContDiffOn ℝ 1
      (fun p : ℝ × V => fderiv ℝ (fderiv ℝ (euclideanGauge (fun x => u p.1 (I x)))) p.2)
      (J ×ˢ univ) := by
  have hc : ContDiffOn ℝ 1 (fun p : ℝ × V => u p.1 (I p.2)) (J ×ˢ univ) :=
    hu.comp (contDiffOn_fst.prodMk (I.contDiff.comp_contDiffOn contDiffOn_snd))
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hs' (t : ℝ) (ht : t ∈ J) : ContDiff ℝ ∞ (fun x : V => u t (I x)) :=
    (hs t ht).comp I.contDiff
  have hd := fderiv_joint_c1_of_first_jet (u := fun t x => u t (I x)) (J := J)
    (restricted_spatial_jet_joint_c1 I hs 1 (hj 1))
  have hdd := hessian_joint_c1_of_second_jet (u := fun t x => u t (I x)) (J := J)
    (restricted_spatial_jet_joint_c1 I hs 2 (hj 2))
  exact ⟨hc.exp.smul contDiffOn_snd, euclideanGauge_fderiv_joint_c1 hs' hc hd,
    euclideanGauge_hessian_joint_c1 hs' hc hd hdd⟩

end PoincareConjecture.M35.RadialGauge
