import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalCrossing
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_interior_return_velocity_ne
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {s t T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (h0 : ‖gamma 0‖ = 1) (hinside : ∀ x ∈ Ioc 0 T, 1 < ‖gamma x‖)
    (hreturn : gamma s = gamma t) : deriv gamma s ≠ deriv gamma t := by
  have hspos : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := le_antisymm (le_of_not_gt hn) hs
    have hnorm := hinside t ⟨by linarith, ht⟩
    rw [← hreturn, hs0, h0] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  intro hvel
  let eta : ℝ → AnnulusCoordinates := fun x => gamma (x + (t - s))
  have he : G.IsGeodesicOn eta (Icc 0 s) := by
    intro x hx
    apply hgeo.comp_add (t - s)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hg' : G.IsGeodesicOn gamma (Icc 0 s) :=
    fun x hx => hgeo x ⟨hx.1, hx.2.trans (hst.le.trans ht)⟩
  have hetas : eta s = gamma t := by
    dsimp only [eta]
    congr 1
    ring
  have hd : HasDerivAt eta (deriv gamma t) s := by
    have h := ((hg.differentiable (by simp) (s + (t - s))).hasDerivAt).scomp s
      ((hasDerivAt_id s).add_const (t - s))
    simpa only [eta, Function.comp_def, id_eq, one_smul,
      show s + (t - s) = t by ring] using! h
  have hcoord : deriv (fun x => extChartAt (𝓡 2) (gamma s) (gamma x)) s =
      deriv (fun x => extChartAt (𝓡 2) (gamma s) (eta x)) s := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using hvel.trans hd.deriv.symm
  have heq := hg'.eq_nhds_on_of_initial_data he (convex_Icc _ _).isPreconnected
    (t₀ := s) ⟨hs, le_rfl⟩ (gamma s) (by simp)
    (hreturn.trans hetas.symm) hcoord
  have hback : gamma 0 = gamma (t - s) := by
    simpa only [eta, zero_add] using
      (heq 0 (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs⟩)).self_of_nhds
  have hnorm := hinside (t - s) ⟨sub_pos.mpr hst, by linarith⟩
  rw [← hback, h0] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

theorem m64Intrinsic_regular_return_velocity_ne_neg
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {s t : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc s t))
    (hst : s < t) (hregular : ∀ x ∈ Icc s t, deriv gamma x ≠ 0)
    (hreturn : gamma s = gamma t) : deriv gamma s ≠ -deriv gamma t := by
  intro hvel
  let eta : ℝ → AnnulusCoordinates := fun x => gamma (-1 * x + (s + t))
  have he : G.IsGeodesicOn eta (Icc s t) := by
    intro x hx
    apply hgeo.comp_affine (-1) (s + t)
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd (x : ℝ) : HasDerivAt eta (-deriv gamma (-1 * x + (s + t))) x := by
    have h := ((hg.differentiable (by simp) (-1 * x + (s + t))).hasDerivAt).scomp x
      (((hasDerivAt_id x).const_mul (-1)).add_const (s + t))
    simpa only [eta, Function.comp_def, id_eq, mul_one, neg_one_smul] using! h
  have hetas : eta s = gamma t := by
    dsimp only [eta]
    congr 1
    ring
  have hds : deriv eta s = -deriv gamma t := by
    simpa only [show -1 * s + (s + t) = t by ring] using (hd s).deriv
  have hcoord : deriv (fun x => extChartAt (𝓡 2) (gamma s) (gamma x)) s =
      deriv (fun x => extChartAt (𝓡 2) (gamma s) (eta x)) s := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using hvel.trans hds.symm
  have heq := hgeo.eq_nhds_on_of_initial_data he (convex_Icc _ _).isPreconnected
    (t₀ := s) ⟨le_rfl, hst.le⟩ (gamma s) (by simp)
    (hreturn.trans hetas.symm) hcoord
  let m : ℝ := (s + t) / 2
  have hm : m ∈ Icc s t := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hmEq : -1 * m + (s + t) = m := by dsimp [m]; ring
  have hder : deriv gamma m = -deriv gamma m := by
    have h := (heq m hm).deriv_eq.trans (hd m).deriv
    simpa only [hmEq] using h
  apply hregular m hm
  have htwice : (2 : ℝ) • deriv gamma m = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hder
  exact (smul_eq_zero.mp htwice).resolve_left (by norm_num)

theorem m64Intrinsic_unit_interior_return_transverse
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {s t T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (h0 : ‖gamma 0‖ = 1) (hinside : ∀ x ∈ Ioc 0 T, 1 < ‖gamma x‖)
    (hunit : ∀ x ∈ Icc 0 T, G.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1)
    (hreturn : gamma s = gamma t) :
    LinearIndependent ℝ (![deriv gamma s, -deriv gamma t] : Fin 2 → AnnulusCoordinates) := by
  have hsI : s ∈ Icc 0 T := ⟨hs, hst.le.trans ht⟩
  have htI : t ∈ Icc 0 T := ⟨hs.trans hst.le, ht⟩
  have hreg (x : ℝ) (hx : x ∈ Icc 0 T) : deriv gamma x ≠ 0 := by
    intro hz
    have h := hunit x hx
    simp only [hz, map_zero] at h
    norm_num at h
  have hsame := m64Intrinsic_interior_return_velocity_ne G hg hgeo hs hst ht h0 hinside hreturn
  have hopp := m64Intrinsic_regular_return_velocity_ne_neg G hg
    (fun x hx => hgeo x ⟨hs.trans hx.1, hx.2.trans ht⟩) hst
    (fun x hx => hreg x ⟨hs.trans hx.1, hx.2.trans ht⟩) hreturn
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨neg_ne_zero.mpr (hreg t htI), ?_⟩
  intro c hc
  have hw : G.inner (gamma s) (deriv gamma t) (deriv gamma t) = 1 := by
    rw [hreturn]
    exact hunit t htI
  have hsq : c ^ 2 = 1 := by
    have h := hunit s hsI
    rw [← hc] at h
    simp only [map_smul, smul_apply, smul_eq_mul, map_neg, neg_apply, hw] at h
    nlinarith only [h]
  have hcCases : c = 1 ∨ c = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hsq)
  rcases hcCases with rfl | rfl
  · apply hopp
    simpa only [one_smul] using hc.symm
  · apply hsame
    simpa only [neg_one_smul, neg_neg] using hc.symm

end PoincareConjecture
