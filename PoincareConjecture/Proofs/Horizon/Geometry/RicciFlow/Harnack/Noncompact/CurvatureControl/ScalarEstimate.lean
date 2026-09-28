import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.PointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Profile

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

private lemma scalar_cutoff_error_absorption
    {N S E Q L : ℝ} (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hQ : 0 < Q) (hL : 1 ≤ L) (hlarge : 4 * E * (N + 2 * S) ≤ L) :
    E * (N * Real.sqrt Q / (L / (2 * Real.sqrt Q)) +
      S / (L / (2 * Real.sqrt Q)) ^ 2) ≤ Q / 2 := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have heq : N * Real.sqrt Q / (L / (2 * Real.sqrt Q)) +
      S / (L / (2 * Real.sqrt Q)) ^ 2 =
      (2 * N / L + 4 * S / L ^ 2) * Q := by
    field_simp
    rw [Real.sq_sqrt hQ.le]
    ring
  have hLs : L ≤ L ^ 2 := by nlinarith
  have hdiv : S / L ^ 2 ≤ S / L :=
    div_le_div_of_nonneg_left hS hLpos hLs
  have hsum : 2 * N / L + 4 * S / L ^ 2 ≤ (2 * N + 4 * S) / L := by
    rw [add_div]
    exact add_le_add_right (by simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 4)) _
  have hcoeff : E * ((2 * N + 4 * S) / L) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hLpos).mpr
    nlinarith
  rw [heq, ← mul_assoc]
  calc
    _ ≤ (E * ((2 * N + 4 * S) / L)) * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hE) hQ.le
    _ ≤ (1 / 2) * Q := mul_le_mul_of_nonneg_right hcoeff hQ.le
    _ = Q / 2 := by ring

private lemma scalar_cutoff_radius_exp_bound {D K : ℝ} (hD : 1 ≤ D) (hK : 1 ≤ K) :
    4 * (D * Real.exp (8 * K)) ^ 2 ≤ Real.exp ((16 + Real.log (4 * D ^ 2)) * K) := by
  have hDsq : 1 ≤ 4 * D ^ 2 := by nlinarith
  have hlog : 0 ≤ Real.log (4 * D ^ 2) := Real.log_nonneg hDsq
  have hcoeff : 4 * D ^ 2 ≤ Real.exp (Real.log (4 * D ^ 2) * K) := by
    calc
      _ = Real.exp (Real.log (4 * D ^ 2)) :=
        (Real.exp_log (zero_lt_one.trans_le hDsq)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right hlog hK)
  calc
    _ = (4 * D ^ 2) * (Real.exp (8 * K) * Real.exp (8 * K)) := by ring
    _ = (4 * D ^ 2) * Real.exp (16 * K) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (Real.log (4 * D ^ 2) * K) * Real.exp (16 * K) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem exists_local_scalar_curvature_constant_of_finite
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M]
        (hTheory : RicciFlowCurvatureTheory.{u})
        (J : Set ℝ) (F : RicciFlow (m + 1) M J)
        (a b r K : ℝ),
        Icc a b ⊆ interior J → 0 < r → 1 ≤ K →
        (∀ t ∈ Icc a b, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
          0 ≤ (F.connection t).ricci x v v) →
        ∀ p : M,
        (∀ x ∈ (F.metric a).ball p r,
          (F.connection a).scalarCurvature x ≤ 1 / r ^ 2) →
        (∀ t ∈ Ioc a b, ∀ x ∈ (F.metric t).ball p r,
          (F.connection t).scalarCurvature x ≤ K / (t - a)) →
        ∀ t ∈ Icc a b, ∀ x ∈ (F.metric t).ball p r,
          (F.connection t).scalarCurvature x ≤
            Real.exp (C * K) / (r - ((F.metric t).edist p x).toReal) ^ 2 := by
  obtain ⟨χ, A, B, C₀, hApos, hBpos, hCpos, hχ, hanti, hrange, hflat, hzero,
    hA, hB, hC⟩ := Poincare.Analysis.exists_radial_cutoff_profile
  let N : ℝ := C₀ * (4 * ((m + 1 : ℕ) : ℝ) + 32)
  let S : ℝ := B + 2 * A + 2 * (m : ℝ) * C₀
  let D : ℝ := 4 * (N + 2 * S) + 1
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  have hlog : 0 ≤ Real.log (4 * D ^ 2) := Real.log_nonneg (by nlinarith)
  refine ⟨16 + Real.log (4 * D ^ 2), by positivity, ?_⟩
  intro M _ _ _ _ hTheory J F a b r K hJ hr hK hcomplete hRic p hinit htime t ht x hx
  let L := D * Real.exp (8 * K)
  have hE : 1 ≤ Real.exp (8 * K) := Real.one_le_exp_iff.mpr (by linarith)
  have hL : 1 ≤ L := by
    dsimp only [L]
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hE)]
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hlarge : 4 * Real.exp (8 * K) * (N + 2 * S) ≤ L := by
    dsimp only [L, D]
    nlinarith only [Real.exp_nonneg (8 * K)]
  let ε := r - ((F.metric t).edist p x).toReal
  have hdist : ((F.metric t).edist p x).toReal < r := by
    change (F.metric t).edist p x < ENNReal.ofReal r at hx
    rw [← ENNReal.ofReal_toReal (ne_top_of_lt hx)] at hx
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hx
  have hε : 0 < ε := sub_pos.mpr hdist
  have hεr : ε ≤ r := sub_le_self _ ENNReal.toReal_nonneg
  have hbound : (F.connection t).scalarCurvature x ≤ 4 * L ^ 2 / ε ^ 2 := by
    by_contra! hbad
    have hRpos : 0 < (F.connection t).scalarCurvature x :=
      lt_of_le_of_lt (by positivity) hbad
    have hinitlt : 1 / r ^ 2 < (F.connection t).scalarCurvature x := by
      calc
        _ ≤ 1 / ε ^ 2 := div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hε)
          ((sq_le_sq₀ hε.le hr.le).mpr hεr)
        _ ≤ 4 * L ^ 2 / ε ^ 2 := div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg ε)
        _ < _ := hbad
    have hsqrt₀ : 0 < Real.sqrt ((F.connection t).scalarCurvature x) := Real.sqrt_pos.mpr hRpos
    have hbudget : 2 * L / Real.sqrt ((F.connection t).scalarCurvature x) < ε := by
      apply (div_lt_iff₀ hsqrt₀).mpr
      have hbad' := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hbad
      have hsq := Real.sq_sqrt hRpos.le
      have hprod : (2 * L) ^ 2 <
          (ε * Real.sqrt ((F.connection t).scalarCurvature x)) ^ 2 := by
        rw [mul_pow ε, hsq]
        nlinarith only [hbad']
      exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hprod
    obtain ⟨τ, hτ, y, hy, hRy, hrad, hlocal⟩ :=
      F.exists_scalarCurvature_point_with_doubling_bound hTheory hJ
        (hcomplete b ⟨ht.1.trans ht.2, le_rfl⟩) hRic p r hLpos.le ht hx hRpos
    let Q := (F.connection τ).scalarCurvature y
    let d := ((F.metric τ).edist p y).toReal
    have hQ : 0 < Q := hRpos.trans_le hRy
    have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
    have hτb : τ ∈ Icc a b := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hmargin : d + 2 * L / Real.sqrt Q < r := by
      change d + 2 * L / Real.sqrt Q ≤ _ at hrad
      dsimp only [ε] at hbudget
      linarith
    have hτa : a < τ := by
      by_contra! hh
      have heq : τ = a := le_antisymm hh hτ.1
      have hinitial := hinit y (by simpa only [heq] using hy)
      rw [← heq] at hinitial
      linarith
    have hQt : Q * (τ - a) ≤ K :=
      (le_div_iff₀ (sub_pos.mpr hτa)).mp (htime τ ⟨hτa, hτb.2⟩ y hy)
    let δ := L / (2 * Real.sqrt Q)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hδeq : 2 * δ = L / Real.sqrt Q := by dsimp only [δ]; ring
    have hradius : d + 2 * δ < r := by
      rw [hδeq]
      have hh : 0 < L / Real.sqrt Q := div_pos hLpos hsqrt
      rw [mul_div_assoc] at hmargin
      linarith
    have hsub (s : ℝ) : (F.metric s).ball p (d + 2 * δ) ⊆ (F.metric s).ball p r := by
      intro z hz
      exact lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hradius.le)
    have hQlocal (s : ℝ) (hs : s ∈ Icc a τ) (z : M)
        (hz : z ∈ (F.metric s).ball p (d + 2 * δ)) :
        (F.connection s).scalarCurvature z ≤ 4 * Q := by
      apply hlocal s hs z (hsub s hz)
      change (F.metric s).edist p z < ENNReal.ofReal (d + 2 * δ) at hz
      rw [← ENNReal.ofReal_toReal (ne_top_of_lt hz)] at hz
      have hradiuspos : 0 < d + 2 * δ := by dsimp only [d]; positivity
      have hh := (ENNReal.ofReal_lt_ofReal_iff hradiuspos).mp hz
      rw [hδeq] at hh
      exact hh.le
    have hJ' : Icc a τ ⊆ interior J := fun s hs => hJ ⟨hs.1, hs.2.trans hτb.2⟩
    have hcomp := F.distance_cutoff_mul_scalarCurvature_le_exp_of_finite hTheory hJ' hm
      (fun s hs => hcomplete s ⟨hs.1, hs.2.trans hτb.2⟩)
      (fun s hs => hRic s ⟨hs.1, hs.2.trans hτb.2⟩) p hδ
      ENNReal.toReal_nonneg (show 0 < 4 * Q by positivity)
      (show 0 ≤ 1 / r ^ 2 by positivity) hsqrt hχ hanti hrange hflat hzero
      hApos.le hBpos.le hCpos.le hA hB hC hQlocal
      (fun z hz => hinit z (hsub a hz)) τ ⟨hτ.1, le_rfl⟩ y
      (ne_top_of_lt hy)
    let H := C₀ * (4 * ((m + 1 : ℕ) : ℝ) * Real.sqrt Q + 8 * (4 * Q) / Real.sqrt Q) / δ +
      S / δ ^ 2
    have hH : 0 ≤ H := by dsimp only [H]; positivity
    have hcutoff : χ ((d - d) / δ) = 1 := hflat _ (by simp)
    change χ ((d - d) / δ) * Q ≤
      Real.exp (2 * (4 * Q) * (τ - a)) * (1 / r ^ 2 + H / 2) - H / 2 at hcomp
    rw [hcutoff, one_mul] at hcomp
    have hHeq : H = N * Real.sqrt Q / δ + S / δ ^ 2 := by
      dsimp only [H, N]
      congr 2
      field_simp
      rw [Real.sq_sqrt hQ.le]
      ring
    have herror : Real.exp (8 * K) * H ≤ Q / 2 := by
      rw [hHeq]
      exact scalar_cutoff_error_absorption hS (Real.exp_nonneg _) hQ hL hlarge
    have hexp : Real.exp (2 * (4 * Q) * (τ - a)) ≤ Real.exp (8 * K) :=
      Real.exp_le_exp.mpr (by nlinarith only [hQt])
    have hcomp' := hcomp.trans (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hexp (by positivity)) (H / 2))
    have hQupper : Q ≤ 2 * Real.exp (8 * K) / r ^ 2 := by
      rw [mul_add, ← mul_div_assoc, mul_one, ← mul_div_assoc] at hcomp'
      rw [mul_div_assoc]
      have hterm : Real.exp (8 * K) * H / 2 - H / 2 ≤ Q / 4 := by
        have hterm' : Real.exp (8 * K) * H / 2 - H / 2 ≤
            Real.exp (8 * K) * H / 2 := by nlinarith [hH]
        nlinarith [herror, hterm']
      linarith [hcomp', hterm]
    have hRlower : 4 * L ^ 2 / r ^ 2 < Q := by
      calc
        _ ≤ 4 * L ^ 2 / ε ^ 2 := div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos hε) ((sq_le_sq₀ hε.le hr.le).mpr hεr)
        _ < (F.connection t).scalarCurvature x := hbad
        _ ≤ Q := hRy
    have hLsq : 2 * Real.exp (8 * K) ≤ 4 * L ^ 2 := by
      have hEL : Real.exp (8 * K) ≤ L := by dsimp only [L]; nlinarith
      nlinarith
    have hcontra := div_le_div_of_nonneg_right hLsq (sq_nonneg r)
    linarith
  exact hbound.trans (div_le_div_of_nonneg_right
    (scalar_cutoff_radius_exp_bound hD hK) (sq_nonneg ε))

theorem exists_local_scalar_curvature_constant
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M]
        (hTheory : RicciFlowCurvatureTheory.{u})
        (J : Set ℝ) (F : RicciFlow (m + 1) M J)
        (a b r K : ℝ),
        Icc a b ⊆ interior J → 0 < r → 1 ≤ K →
        (∀ t ∈ Icc a b, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
          0 ≤ (F.connection t).ricci x v v) →
        ∀ p : M,
        (∀ x ∈ (F.metric a).ball p r,
          (F.connection a).scalarCurvature x ≤ 1 / r ^ 2) →
        (∀ t ∈ Ioc a b, ∀ x ∈ (F.metric t).ball p r,
          (F.connection t).scalarCurvature x ≤ K / (t - a)) →
        ∀ t ∈ Icc a b, ∀ x ∈ (F.metric t).ball p r,
          (F.connection t).scalarCurvature x ≤
            Real.exp (C * K) / (r - ((F.metric t).edist p x).toReal) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_local_scalar_curvature_constant_of_finite m hm
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ hTheory J F a b r K
  exact h M hTheory J F a b r K

end PoincareConjecture.RicciFlow
