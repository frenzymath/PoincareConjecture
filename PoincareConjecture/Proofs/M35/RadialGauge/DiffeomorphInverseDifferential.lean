import PoincareConjecture.Proofs.M35.RadialGauge.DiffeomorphFamilyInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem diffeomorph_fderiv_symm_eq_inverse
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞) (y : V) :
    fderiv ℝ (Φ.symm : V → V) y =
      (fderiv ℝ (Φ : V → V) (Φ.symm y)).inverse := by
  have hs : ContDiff ℝ ∞ (Φ : V → V) := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hsi : ContDiff ℝ ∞ (Φ.symm : V → V) := contMDiff_iff_contDiff.mp Φ.symm.contMDiff
  apply (ContinuousLinearMap.inverse_eq ?_ ?_).symm
  · have h := fderiv_comp y (hs.differentiable (by simp) (Φ.symm y))
      (hsi.differentiable (by simp) y)
    have he : (Φ : V → V) ∘ (Φ.symm : V → V) = id := funext Φ.apply_symm_apply
    rw [he, fderiv_id] at h
    exact h.symm
  · have h := fderiv_comp (Φ.symm y)
      (hsi.differentiable (by simp) (Φ (Φ.symm y)))
      (hs.differentiable (by simp) (Φ.symm y))
    have he : (Φ.symm : V → V) ∘ (Φ : V → V) = id := funext Φ.symm_apply_apply
    rw [he, fderiv_id, Φ.apply_symm_apply] at h
    exact h.symm

theorem diffeomorph_family_symm_fderiv_contDiffAt
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (fun p : ℝ × V => Φ p.1 p.2) (J ×ˢ univ))
    (hdc : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (Φ p.1 : V → V) p.2)
      (J ×ˢ univ))
    {p : ℝ × V} (hp : p.1 ∈ J) :
    ContDiffAt ℝ 1 (fun z : ℝ × V => fderiv ℝ ((Φ z.1).symm : V → V) z.2) p := by
  have hi := diffeomorph_family_symm_contDiffAt hJ hc hp
  have hpair : ContDiffAt ℝ 1 (fun z : ℝ × V => (z.1, (Φ z.1).symm z.2)) p :=
    contDiffAt_fst.prodMk hi
  have hD : ContDiffAt ℝ 1
      (fun z : ℝ × V => fderiv ℝ (Φ z.1 : V → V) ((Φ z.1).symm z.2)) p := by
    have hb : ContDiffAt ℝ 1 (fun z : ℝ × V => fderiv ℝ (Φ z.1 : V → V) z.2)
        (p.1, (Φ p.1).symm p.2) :=
      hdc.contDiffAt ((hJ.prod isOpen_univ).mem_nhds
        ⟨hp, mem_univ ((Φ p.1).symm p.2)⟩)
    exact hb.comp p hpair
  have hInv : (fderiv ℝ (Φ p.1 : V → V) ((Φ p.1).symm p.2)).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using
      DiffeomorphNative.mfderiv_isInvertible (Φ p.1) ((Φ p.1).symm p.2)
  have h := hInv.contDiffAt_map_inverse.comp p hD
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall (fun z => diffeomorph_fderiv_symm_eq_inverse (Φ z.1) z.2)

theorem diffeomorph_family_symm_fderiv_continuous
    {S : Type*} [TopologicalSpace S]
    {Φ : S → Diffeomorph (𝓡 n) (𝓡 n) V V ∞}
    (hdc : Continuous (fun p : S × V => fderiv ℝ (Φ p.1 : V → V) p.2))
    (hic : Continuous (fun p : S × V => (Φ p.1).symm p.2)) :
    Continuous (fun p : S × V => fderiv ℝ ((Φ p.1).symm : V → V) p.2) := by
  have hD : Continuous
      (fun p : S × V => fderiv ℝ (Φ p.1 : V → V) ((Φ p.1).symm p.2)) :=
    hdc.comp (continuous_fst.prodMk hic)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hInv : (fderiv ℝ (Φ p.1 : V → V) ((Φ p.1).symm p.2)).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using
      DiffeomorphNative.mfderiv_isInvertible (Φ p.1) ((Φ p.1).symm p.2)
  have h := (hInv.contDiffAt_map_inverse (n := 0)).continuousAt.comp
    (f := fun z : S × V => fderiv ℝ (Φ z.1 : V → V) ((Φ z.1).symm z.2)) hD.continuousAt
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall (fun z => diffeomorph_fderiv_symm_eq_inverse (Φ z.1) z.2)

end PoincareConjecture.M35.RadialGauge
