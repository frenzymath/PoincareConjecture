import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.C2.IntegratedEstimates
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Energy

/-!
# C2 estimates supplied by the actual local curve theory

On each positive subslab, the local theory supplies a fixed relabeling of
an actual smooth curve. M62 applies to the literal restricted flow with the
original bounds; the checked transport and endpoint arguments fill the
entire frozen C2 estimate record. This is conditional on the local theory,
which remains a separate M63 obligation. Source: MT2015Correction pp. 6-8;
see `2026-09-21-c2-estimates-from-local.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M] {a b T : ℝ}

/-- The actual local curve theory and M62 imply every frozen C2 estimate
with the same ambient constants, through the original included endpoints.
Corrected Corollary 0.3, Lemma 0.4 and Corollary 19.10, pp. 6-8. -/
theorem c2_estimates_of_local (hM62 : M62CurveEvolutionTheory.{u})
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hlocal : M63LocalCurveTheory F) {K0 K1 K2 : ℝ}
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (c : ℝ → ℝ → M) (hc : M63C2ShrinkingCurveOn F c (Icc a T)) (hT : a < T) :
    M63C2CurveEstimates F c T K0 K1 K2 := by
  have hTb : T ≤ b := (hc.domain_subset ⟨hT.le, le_rfl⟩).2
  have hchart (tau s : ℝ) (hatau : a < tau) (htaus : tau < s) (hsT : s ≤ T) :
      let Fs := m63RestrictClosedFlow F tau s
        (Icc_subset_Icc hatau.le (hsT.trans hTb)) htaus
      ∃ (phi : ℝ → ℝ) (d : ℝ → ℝ → M),
        ContDiff ℝ 2 phi ∧ (∀ y, 0 < deriv phi y) ∧
        (∀ y, phi (y + curvePeriod) = phi y + curvePeriod) ∧
        M62ShrinkingCurve Fs d ∧ M62CurveEstimates Fs d K0 K1 K2 ∧
        ∀ r ∈ Icc tau s, ∀ y, c y r = d (phi y) r := by
    obtain ⟨phi, d, hphi, _, hpos, hshift, hd, _, hcd⟩ :=
      hlocal.fixed_relabeling T hT hTb (Icc a T) (Or.inl rfl) c hc tau s
        hatau htaus hsT (Icc_subset_Icc hatau.le hsT)
    refine ⟨phi, d, hphi, hpos, hshift, ?_, ?_, hcd⟩
    · exact m63SmoothRestriction hd tau s Subset.rfl htaus
    · exact m63M62RestrictedEstimates hM62 hcompact hK0 hK1 hK2 hBounds
        hd tau s Subset.rfl htaus
  apply c2_estimates_of_interior F c hc hT hK0 hK1 hK2
  · intro epsilon hepsilon t ht x
    obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
    obtain ⟨s, hts, hsT⟩ := exists_between ht.2
    obtain ⟨phi, d, hphi, hpos, _, hd, hE, hcd⟩ :=
      hchart tau s hatau (htaut.trans hts) hsT.le
    exact regularized_time_of_relabeling _ hd (hphi.differentiable (by norm_num))
      hpos hcd hE hepsilon ⟨htaut, hts⟩
  · intro epsilon hepsilon t ht x
    obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
    obtain ⟨s, hts, hsT⟩ := exists_between ht.2
    obtain ⟨phi, d, hphi, hpos, _, hd, hE, hcd⟩ :=
      hchart tau s hatau (htaut.trans hts) hsT.le
    exact regularized_bound_of_relabeling _ hd (hphi.differentiable (by norm_num))
      hpos hcd hE hepsilon ⟨htaut, hts⟩
  · intro t ht
    obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
    obtain ⟨s, hts, hsT⟩ := exists_between ht.2
    obtain ⟨phi, d, hphi, hpos, hshift, hd, hE, hcd⟩ :=
      hchart tau s hatau (htaut.trans hts) hsT.le
    exact length_derivative_of_relabeling
      (m63RestrictClosedFlow F tau s (Icc_subset_Icc hatau.le (hsT.le.trans hTb))
        (htaut.trans hts)) hd (hphi.of_le (by norm_num)) hpos hshift hcd hE ⟨htaut, hts⟩
  · intro t ht
    obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
    obtain ⟨s, hts, hsT⟩ := exists_between ht.2
    obtain ⟨phi, d, hphi, hpos, hshift, hd, hE, hcd⟩ :=
      hchart tau s hatau (htaut.trans hts) hsT.le
    exact length_energy_bound_of_relabeling _ hd (hphi.of_le (by norm_num))
      hpos hshift hcd hE ⟨htaut, hts⟩
  · intro s t hs ht hst
    obtain ⟨tau, hatau, htaus⟩ := exists_between hs.1
    obtain ⟨phi, d, hphi, hpos, hshift, hd, hE, hcd⟩ :=
      hchart tau t hatau (htaus.trans_le hst) ht.2.le
    exact total_curvature_integral_of_relabeling _ hd (hphi.of_le (by norm_num))
      hpos hshift hcd hE ⟨htaus.le, hst⟩ ⟨(htaus.trans_le hst).le, le_rfl⟩ hst

end PoincareMT.M63
