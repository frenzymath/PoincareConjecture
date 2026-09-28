import PoincareConjecture.Proofs.M34.Standard.SectionalModelParameters
import PoincareConjecture.Proofs.M34.Standard.SectionalNormLower
import PoincareConjecture.Proofs.M34.Standard.SectionalBarrierVelocity
import PoincareConjecture.Proofs.M34.Standard.ProperBarrierComparison
import PoincareConjecture.Proofs.M10.ScalarBound
import PoincareConjecture.Proofs.M10.LaplacianLinearity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open M04

theorem nonnegativeSectionalCurvature_of_proper_barrier
    {T B C : ℝ} (hT : 0 < T) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).curvatureTensorNorm x ≤ B)
    (hinit : (F.connection 0).NonnegativeSectionalCurvature)
    (rho : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hrho : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ rho) (hrho1 : ∀ x, 1 ≤ rho x)
    (hcompact : ∀ R : ℝ, IsCompact {x | rho x ≤ R})
    (hlap : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).laplacian rho x ≤ C * rho x) :
    ∀ t ∈ Icc 0 T, (F.connection t).NonnegativeSectionalCurvature := by
  let E := EuclideanSpace ℝ (Fin 3)
  let q := fun s (z : E × (E × E)) =>
    (F.connection s).curvatureTensor z.1 z.2.1 z.2.2 z.2.1 z.2.2 /
      metricGram (F.metric s) z.1 z.2.1 z.2.2
  have hgram (s : ℝ) (x : E) (p : E × E) (hp : p ∈ modelOrthonormalPairs 3) :
      0 < metricGram (F.metric s) x p.1 p.2 :=
    metricGram_pos_of_linearIndependent _ _ _ _ (modelOrthonormalPairs_linearIndependent hp)
  have hlow (s : ℝ) (hs : s ∈ Icc 0 T) (z : E × (E × E))
      (hz : z.2 ∈ modelOrthonormalPairs 3) : -B ≤ q s z :=
    (neg_le_neg (hbound s hs z.1)).trans
      (neg_curvatureTensorNorm_le_sectionalRayleigh (F.connection s) z.1 z.2.1 z.2.2
        (hgram s z.1 z.2 hz))
  have hscalar (s : ℝ) (hs : s ∈ Icc 0 T) (x : E) :
      (F.connection s).scalarCurvature x ≤ 9 * B := by
    have h := M10.abs_scalarCurvature_le (F.metric s) (F.connection s) x
    norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at h
    exact (le_abs_self _).trans (h.trans
      (mul_le_mul_of_nonneg_left (hbound s hs x) (by norm_num)))
  have hplanes : ∀ t ∈ Icc 0 T, ∀ x : E, ∀ p ∈ modelOrthonormalPairs 3,
      0 ≤ q t (x, p) := by
    intro t ht x p hp
    by_contra hbad
    have hneg : q t (x, p) < 0 := lt_of_not_ge hbad
    let A := 11 * B
    let L := C + A
    have hL : 0 ≤ L := add_nonneg hC (mul_nonneg (by norm_num) hB)
    let eps := -q t (x, p) / (2 * Real.exp (L * t) * rho x)
    have heps : 0 < eps := div_pos (neg_pos.mpr hneg)
      (mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
        (lt_of_lt_of_le zero_lt_one (hrho1 x)))
    let R := max (rho x + 1) (B / eps + 1)
    let K : Set E := {y | rho y ≤ R}
    let S := K ×ˢ modelOrthonormalPairs 3
    have hxK : x ∈ K :=
      (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans (le_max_left _ _)
    have hepsR : B < eps * R := by
      have h := mul_le_mul_of_nonneg_left (le_max_right (rho x + 1) (B / eps + 1)) heps.le
      have hcanc : eps * (B / eps) = B := by field_simp
      rw [mul_add, hcanc, mul_one] at h
      dsimp only [R]
      linarith
    let w := fun s (z : E × (E × E)) => q s z + eps * Real.exp (L * s) * rho z.1
    let velocity := fun s (z : E × (E × E)) =>
      sectionalRayleighVelocity (F.connection s) z.1 z.2.1 z.2.2 +
        eps * Real.exp (L * s) * L * rho z.1
    have hw : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ S) := by
      apply ((continuousOn_flow_sectionalRayleigh_model F).mono
        (prod_mono (Subset.refl _) (prod_mono (subset_univ K) (Subset.refl _)))).add
      exact ((continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).mul
        (hrho.continuous.comp continuous_snd.fst)).continuousOn
    have hdw : ∀ s ∈ Icc 0 T, ∀ z ∈ S,
        HasDerivWithinAt (fun r => w r z) (velocity s z) (Icc 0 T) s := by
      intro s hs z hz
      have hdq := hasDerivWithinAt_sectionalRayleighVelocity F s hs z.1 z.2.1 z.2.2
        (hgram s z.1 z.2 hz.2)
      have hdexp := ((hasDerivAt_id s).const_mul L).exp
      have hb := ((hdexp.const_mul eps).mul_const (rho z.1)).hasDerivWithinAt
        (s := Icc 0 T)
      convert! hdq.add hb using 1
      simp only [id_eq, mul_one]
      ring
    have hwinit (z : E × (E × E)) (hz : z ∈ S) : 0 ≤ w 0 z := by
      have hq0 : 0 ≤ q 0 z := div_nonneg (hinit z.1 z.2.1 z.2.2)
        (hgram 0 z.1 z.2 hz.2).le
      have hterm := mul_nonneg heps.le (le_trans zero_le_one (hrho1 z.1))
      simpa only [w, mul_zero, Real.exp_zero, mul_one] using add_nonneg hq0 hterm
    have hwmin : ∀ s ∈ Ioc 0 T, ∀ z ∈ S,
        (∀ y ∈ S, w s z ≤ w s y) → w s z < 0 →
          -(-A) * w s z ≤ velocity s z := by
      intro s hs z hz hmin hwneg
      have hsJ : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
      let a := eps * Real.exp (L * s)
      have ha : 0 ≤ a := mul_nonneg heps.le (Real.exp_nonneg _)
      have hrhoz : 0 ≤ rho z.1 := le_trans zero_le_one (hrho1 z.1)
      have hexp : 1 ≤ Real.exp (L * s) := Real.one_le_exp (mul_nonneg hL hs.1.le)
      have hzlt : rho z.1 < R := by
        by_contra h
        have h1 := mul_le_mul_of_nonneg_left (le_of_not_gt h) heps.le
        have h2 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp heps.le) hrhoz
        have h3 := hlow s hsJ z hz.2
        dsimp only [w] at hwneg
        nlinarith
      let U : Set E := {y | rho y < R}
      have hU : IsOpen U := isOpen_lt hrho.continuous continuous_const
      let f := fun y : E => w s z - a * rho y
      have hpert : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => a * rho y) :=
        (contDiff_const.mul contDiff_id).contMDiff.comp hrho
      have hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f := contMDiff_const.sub hpert
      have hminf : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
          f y * metricGram (F.metric s) y u v ≤
            (F.connection s).curvatureTensor y u v u v := by
        intro y hy u v
        apply sectional_lower_of_model_pairs (F.connection s) y (f y)
        intro p' hp'
        have hyK : y ∈ K := (show rho y < R from hy).le
        have hm := hmin (y, p') ⟨hyK, hp'⟩
        change w s z ≤ q s (y, p') + a * rho y at hm
        change w s z - a * rho y ≤ q s (y, p')
        linarith
      have hfx : f z.1 = q s z := by dsimp only [f, w, a]; ring
      have hnull : (F.connection s).curvatureTensor z.1 z.2.1 z.2.2 z.2.1 z.2.2 =
          f z.1 * metricGram (F.metric s) z.1 z.2.1 z.2.2 := by
        rw [hfx]
        exact (div_mul_cancel₀ _ (hgram s z.1 z.2 hz.2).ne').symm
      have hv := sectionalRayleighVelocity_ge_barrier (F.connection s) hf hU hzlt
        hminf z.2.1 z.2.2 (hgram s z.1 z.2 hz.2) hnull
      have hlapf : (F.connection s).laplacian f z.1 =
          -a * (F.connection s).laplacian rho z.1 := by
        dsimp only [f]
        rw [(F.connection s).laplacian_sub contMDiff_const hpert,
          M10.laplacian_const_scalar, (F.connection s).laplacian_const_mul]
        ring
      rw [hlapf, hfx] at hv
      have hqneg : q s z < 0 := by
        have hpterm := mul_nonneg ha hrhoz
        change q s z + a * rho z.1 < 0 at hwneg
        linarith
      have hcoeff : (F.connection s).scalarCurvature z.1 - 2 * q s z ≤ A := by
        have h1 := hscalar s hsJ z.1
        have h2 := hlow s hsJ z hz.2
        dsimp only [A]
        linarith
      have hreact : A * q s z ≤ q s z *
          ((F.connection s).scalarCurvature z.1 - 2 * q s z) := by
        simpa only [mul_comm] using mul_le_mul_of_nonpos_left hcoeff hqneg.le
      have hbar := mul_le_mul_of_nonneg_left (hlap s hsJ z.1) ha
      change -(-A) * (q s z + a * rho z.1) ≤
        sectionalRayleighVelocity (F.connection s) z.1 z.2.1 z.2.2 + a * L * rho z.1
      dsimp only [L]
      nlinarith only [hv, hreact, hbar]
    have hnonneg := compact_subset_min_velocity_nonnegative
      ((hcompact R).prod (isCompact_modelOrthonormalPairs 3)) (K := -A) hT
      w velocity hw hdw hwmin hwinit t ht (x, p) ⟨hxK, hp⟩
    have heq : eps * Real.exp (L * t) * rho x = -q t (x, p) / 2 := by
      have hrhone : rho x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hrho1 x))
      dsimp only [eps]
      field_simp [hrhone]
    dsimp only [w] at hnonneg
    rw [heq] at hnonneg
    linarith
  intro t ht x u v
  have h := sectional_lower_of_model_pairs (F.connection t) x 0 (hplanes t ht x) u v
  simpa only [zero_mul] using h

end PoincareConjecture.M34
