import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem matrix_det_contDiffOn {s : Set (ℝ × V)}
    {G : ℝ × V → Matrix (Fin n) (Fin n) ℝ} (hG : ContDiffOn ℝ ∞ G s) :
    ContDiffOn ℝ ∞ (fun p => (G p).det) s := by
  have h : ContDiffOn ℝ ∞ (fun p =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, G p (σ i) i) s := by
    apply ContDiffOn.sum
    intro σ _
    apply contDiffOn_const.mul
    apply contDiffOn_prod
    intro i _
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hG (σ i)) i
  convert h using 1
  funext p
  exact Matrix.det_apply' (G p)

theorem rawCoordinateGram_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawCoordinateGram (F.metric p.1) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact raw_metric_pair_family_contDiffOn F (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)

theorem raw_inverseGram_entry_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => (rawCoordinateGram (F.metric p.1) p.2)⁻¹ i j) (J ×ˢ univ) := by
  have hG := rawCoordinateGram_family_contDiffOn F
  have hdet := matrix_det_contDiffOn hG
  have hrow : ContDiffOn ℝ ∞ (fun p : ℝ × V =>
      (rawCoordinateGram (F.metric p.1) p.2).updateRow j (Pi.single i 1)) (J ×ˢ univ) := by
    apply contDiffOn_pi.mpr
    intro r
    apply contDiffOn_pi.mpr
    intro c
    by_cases hr : r = j
    · subst r
      simp only [Matrix.updateRow_apply, if_true]
      exact contDiffOn_const
    · simp only [Matrix.updateRow_apply, hr, if_false]
      exact contDiffOn_pi.mp (contDiffOn_pi.mp hG r) c
  have ha : ContDiffOn ℝ ∞ (fun p : ℝ × V =>
      (rawCoordinateGram (F.metric p.1) p.2).adjugate i j) (J ×ˢ univ) := by
    simpa only [Matrix.adjugate_apply] using matrix_det_contDiffOn hrow
  have hn (p : ℝ × V) (_hp : p ∈ J ×ˢ univ) :
      (rawCoordinateGram (F.metric p.1) p.2).det ≠ 0 :=
    (rawCoordinateGram_posDef (F.metric p.1) p.2).det_pos.ne'
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Pi.inv_apply] using! (hdet.inv hn).mul ha

theorem rawInverseGramDerivative_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (i j : Fin n) : ContDiffOn ℝ ∞ (fun p : ℝ × V =>
      fderiv ℝ (fun x => (rawCoordinateGram (F.metric p.1) x)⁻¹ i j) p.2)
      (J ×ˢ univ) :=
  raw_family_spatial_fderiv_contDiffOn
    (f := fun t x => (rawCoordinateGram (F.metric t) x)⁻¹ i j)
    (raw_inverseGram_entry_family_contDiffOn F i j)

theorem rawRicciLinear_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawRicciLinear (F.connection p.1) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro z
  change ContDiffOn ℝ ∞ (fun p : ℝ × V => RicciFlow.ricciSharp (F.connection p.1) p.2 z) _
  simp only [raw_ricciSharp_inverse_gram]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (raw_inverseGram_entry_family_contDiffOn F i j).smul
    ((raw_ricci_pair_family_contDiffOn F z (EuclideanSpace.single i 1)).smul contDiffOn_const)

end PoincareConjecture.M35.Uniqueness.Heat
