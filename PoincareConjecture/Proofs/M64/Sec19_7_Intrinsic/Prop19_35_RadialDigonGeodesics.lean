import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ClosedRadialGeodesic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_exists_radial_digon_geodesics
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzeroOmega : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (hmetric : ∀ v w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    {v theta : AnnulusCoordinates} {s : ℝ} (hv : v ∈ Omega) (hvne : v ≠ 0)
    (htheta : ‖theta‖ = 1) (hs : 0 < s) (hsv : s • theta ∈ Omega)
    (hpoint : e v = e (s • theta))
    (hcontacts : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc 0 s,
      e (t • v) = e (u • theta) → (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = s)) :
    ∃ alpha beta : ℝ → AnnulusCoordinates,
      ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
      N.metric.IsGeodesicOn alpha (Icc 0 ‖v‖) ∧ N.metric.IsGeodesicOn beta (Icc 0 s) ∧
      (∀ t ∈ Icc 0 ‖v‖, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1) ∧
      (∀ t ∈ Icc 0 s, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1) ∧
      alpha 0 = e 0 ∧ beta 0 = e 0 ∧ alpha ‖v‖ = e v ∧ beta s = e v ∧
      (∀ t ∈ Icc 0 ‖v‖, alpha t = e ((t / ‖v‖) • v)) ∧
      (∀ t ∈ Icc 0 s, beta t = e (t • theta)) ∧
      (∀ t ∈ Icc 0 ‖v‖, ∀ u ∈ Icc 0 s,
        alpha t = beta u → (t = 0 ∧ u = 0) ∨ (t = ‖v‖ ∧ u = s)) ∧
      deriv alpha ‖v‖ = fderiv ℝ e v (‖v‖⁻¹ • v) ∧
      deriv beta s = fderiv ℝ e (s • theta) theta := by
  have hell : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hsnorm : ‖s • theta‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, htheta, mul_one]
  have hsne : s • theta ≠ 0 := by
    intro hz
    exact hs.ne' (by simpa only [hz, norm_zero] using hsnorm.symm)
  obtain ⟨alpha, ha, hga, hua, ha0, haT, hav, _, had⟩ :=
    m64Intrinsic_exists_closed_radial_unit_geodesic N hOmega hzeroOmega he
      hmetric hgeo hstar hv hvne
  obtain ⟨beta, hb, hgb, hub, hb0, hbT, hbv, _, hbd⟩ :=
    m64Intrinsic_exists_closed_radial_unit_geodesic N hOmega hzeroOmega he
      hmetric hgeo hstar hsv hsne
  rw [hsnorm] at hgb hub hbT hbv hbd
  have hbeta (t : ℝ) (ht : t ∈ Icc 0 s) : beta t = e (t • theta) := by
    simpa only [smul_smul, div_mul_cancel₀ _ hs.ne'] using hbv t ht
  refine ⟨alpha, beta, ha, hb, hga, hgb, hua, hub, ha0, hb0, haT,
    hbT.trans hpoint.symm, hav, hbeta, ?_, had, ?_⟩
  · intro t ht u hu hmeet
    have hscale : t / ‖v‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hell.le, (div_le_one hell).mpr ht.2⟩
    rcases hcontacts _ hscale u hu ((hav t ht).symm.trans (hmeet.trans (hbeta u hu))) with h | h
    · exact Or.inl ⟨(div_eq_zero_iff.mp h.1).resolve_right hell.ne', h.2⟩
    · exact Or.inr ⟨(div_eq_one_iff_eq hell.ne').mp h.1, h.2⟩
  · simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using hbd

end PoincareConjecture
