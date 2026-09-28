import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointLowerOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem raw_family_time_fderiv_contDiffOn
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {f : ℝ × V → W}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V =>
      fderivWithin ℝ (fun t => f (t, p.2)) J p.1) (J ×ˢ univ) := by
  intro p hp
  have hmap : MapsTo (fun q : (ℝ × V) × ℝ => (q.2, q.1.2))
      ((J ×ˢ univ) ×ˢ J) (J ×ˢ univ) := fun _ hq => ⟨hq.2, mem_univ _⟩
  have hf' : ContDiffWithinAt ℝ ∞ (fun q : (ℝ × V) × ℝ => f (q.2, q.1.2))
      ((J ×ˢ univ) ×ˢ J) (p, p.1) :=
    (hf p hp).comp (p, p.1)
      (contDiffWithinAt_snd.prodMk contDiffWithinAt_fst.snd) hmap
  exact hf'.fderivWithin contDiffWithinAt_fst hJ
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp) hp (fun _ h => h.1)

theorem raw_family_time_derivative_contDiffOn
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {f : ℝ × V → W}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V =>
      fderivWithin ℝ (fun t => f (t, p.2)) J p.1 1) (J ×ˢ univ) :=
  (raw_family_time_fderiv_contDiffOn hJ hf).clm_apply contDiffOn_const

theorem raw_family_time_hasDerivWithinAt
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {J : Set ℝ} {f : ℝ × V → W}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ)) {t : ℝ} (ht : t ∈ J) (x : V) :
    HasDerivWithinAt (fun s => f (s, x))
      (fderivWithin ℝ (fun s => f (s, x)) J t 1) J t := by
  have hs : ContDiffOn ℝ ∞ (fun s => f (s, x)) J :=
    hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hs => ⟨hs, mem_univ x⟩)
  exact ((hs t ht).differentiableWithinAt (by simp)).hasFDerivWithinAt.hasDerivWithinAt

end PoincareConjecture.M35.Uniqueness.Heat
