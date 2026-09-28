import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusHarmonicMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.PeriodicHarmonicMinimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter InnerProductSpace
open scoped Topology

namespace PoincareConjecture

private theorem modulus_point_coordinates (p : LoopPlane) :
    annulusPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

private theorem modulus_period_reduction {f : LoopPlane → ℝ}
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (p : LoopPlane) (hs : p 1 ∈ Icc (0 : ℝ) 1) :
    ∃ q ∈ m64AnnulusDomain, q 1 = p 1 ∧ f q = f p := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let x := toIcoMod hP 0 (p 0)
  have hx := toIcoMod_mem_Ico' hP (p 0)
  refine ⟨annulusPoint x (p 1), ⟨hx.1, hx.2.le, hs.1, hs.2⟩, rfl, ?_⟩
  have hper : Function.Periodic (fun r => f (annulusPoint r (p 1))) curvePeriod :=
    fun r => hperiod r (p 1)
  have heq := hper.zsmul (toIcoDiv hP 0 (p 0)) x
  dsimp only [x] at heq ⊢
  rw [toIcoMod_add_toIcoDiv_zsmul] at heq
  exact heq.symm.trans (congrArg f (modulus_point_coordinates p))

private theorem modulus_constant_on_domain {f : LoopPlane → ℝ} {c : ℝ}
    (hc : ContinuousOn f m64AnnulusDomain)
    (heq : EqOn f (fun _ => c) m64AnnulusOpenStrip) :
    EqOn f (fun _ => c) m64AnnulusDomain := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusOpenStrip := by
    intro p hp
    change p 1 ∈ Ioo (0 : ℝ) 1
    simpa only [Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      using hp 1 (mem_univ _)
  apply (heq.mono hsub).of_subset_closure hc continuousOn_const
  · rw [← m64AnnulusInterior_closure]
    exact subset_closure
  · rw [m64AnnulusInterior_closure]

theorem m64PeriodicModulus_nonneg_of_boundary_nonneg
    {r : ℝ} (hr : 0 < r) {f : LoopPlane → ℝ}
    (hc : ContinuousOn f m64AnnulusDomain)
    (hf : ContDiffOn ℝ 2 f m64AnnulusOpenStrip)
    (heq : ∀ p ∈ m64AnnulusOpenStrip,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s))
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ f (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ f (annulusPoint x 1)) :
    ∀ p ∈ m64AnnulusOpenStrip, 0 ≤ f p := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hzero : annulusPoint 0 0 ∈ m64AnnulusDomain :=
    ⟨le_rfl, hP.le, le_rfl, zero_le_one⟩
  obtain ⟨p, hp, hmin⟩ := m64AnnulusDomain_isCompact.exists_isMinOn
    ⟨_, hzero⟩ hc
  have hglobal : ∀ q ∈ m64AnnulusOpenStrip, f p ≤ f q := by
    intro q hq
    obtain ⟨r', hr', -, heq'⟩ := modulus_period_reduction hperiod q
      ⟨hq.1.le, hq.2.le⟩
    exact heq' ▸ hmin hr'
  have hnonneg : 0 ≤ f p := by
    by_contra h
    have hneg : f p < 0 := lt_of_not_ge h
    have hs0 : p 1 ≠ 0 := by
      intro hs
      have heq' : annulusPoint (p 0) 0 = p := hs ▸ modulus_point_coordinates p
      have hb := hlower (p 0) ⟨hp.1, hp.2.1⟩
      rw [heq'] at hb
      exact (not_lt_of_ge hb) hneg
    have hs1 : p 1 ≠ 1 := by
      intro hs
      have heq' : annulusPoint (p 0) 1 = p := hs ▸ modulus_point_coordinates p
      have hb := hupper (p 0) ⟨hp.1, hp.2.1⟩
      rw [heq'] at hb
      exact (not_lt_of_ge hb) hneg
    have hpstrip : p ∈ m64AnnulusOpenStrip :=
      ⟨lt_of_le_of_ne hp.2.2.1 hs0.symm, lt_of_le_of_ne hp.2.2.2 hs1⟩
    have heq' := m64ModulusHarmonic_eqOn_of_minimum hr
      isOpen_m64AnnulusOpenStrip isPreconnected_m64AnnulusOpenStrip hf heq
      hpstrip hglobal
    have hboundary := modulus_constant_on_domain hc heq' hzero
    have hb := hlower 0 ⟨le_rfl, hP.le⟩
    rw [hboundary] at hb
    exact (not_lt_of_ge hb) hneg
  exact fun q hq => hnonneg.trans (hglobal q hq)

theorem m64PeriodicModulus_pos_of_boundary_nonneg
    {r : ℝ} (hr : 0 < r) {f : LoopPlane → ℝ}
    (hc : ContinuousOn f m64AnnulusDomain)
    (hf : ContDiffOn ℝ 2 f m64AnnulusOpenStrip)
    (heq : ∀ p ∈ m64AnnulusOpenStrip,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s))
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ f (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ f (annulusPoint x 1))
    (hnonzero : ∃ p ∈ m64AnnulusDomain, f p ≠ 0) :
    ∀ p ∈ m64AnnulusOpenStrip, 0 < f p := by
  have hn := m64PeriodicModulus_nonneg_of_boundary_nonneg hr hc hf heq hperiod
    hlower hupper
  intro p hp
  by_contra h
  have hzero : f p = 0 := le_antisymm (not_lt.mp h) (hn p hp)
  have heq' := m64ModulusHarmonic_eqOn_of_minimum hr
    isOpen_m64AnnulusOpenStrip isPreconnected_m64AnnulusOpenStrip hf heq hp
    (fun q hq => hzero.symm ▸ hn q hq)
  obtain ⟨q, hq, hne⟩ := hnonzero
  exact hne ((modulus_constant_on_domain hc heq' hq).trans hzero)

end PoincareConjecture
