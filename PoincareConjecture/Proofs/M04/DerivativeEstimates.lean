import PoincareConjecture.Definitions.Ch01.TensorOperators
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M04.ShiGeometricCutoff
import PoincareConjecture.Proofs.M04.ShiRecenteredCarrier










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set

universe u

namespace PoincareConjecture

private theorem curvatureDerivativeNorm_zero_dim
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    [IsManifold (𝓡 0) ∞ M]
    (g : RiemannianMetric 0 M) (D : LeviCivitaData g) (m : ℕ) (x : M) :
    D.curvatureDerivativeNorm m x = 0 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 0) x) = 0 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0
    simp
  letI : IsEmpty (Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 0) x))) :=
    ⟨fun a => Fin.elim0 (Fin.cast hdim (a 0))⟩
  simp [LeviCivitaData.curvatureDerivativeNorm, RiemannianMetric.tensorNorm]

private theorem local_curvatureDerivative_bound_zero_core (n : ℕ) (K α r : ℝ)
    (hK : 0 < K) (hα : 0 < α) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
        [T2Space N] [SecondCountableTopology N],
      ∀ (T : ℝ), 0 < T → T ≤ α / K →
      ∀ (F : RicciFlow n N (Set.Icc 0 T)) (p : N),
        IsCompact (closure ((F.metric 0).ball p r)) →
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ (F.metric 0).ball p (r / 2),
          (F.connection t).curvatureDerivativeNorm 0 x ≤ C / t ^ ((0 : ℝ) / 2) := by
  refine ⟨K + 1, by linarith, ?_⟩
  intro N _ _ _ _ _ T hT hTK F p hcompact hRm t ht x hx
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hxouter : x ∈ (F.metric 0).ball p r := by
    exact (M04.initial_half_ball_closure_subset_initial_ball (F.metric 0) p hr)
      (subset_closure hx)
  have hcurv := hRm t htIcc x hxouter
  have hden : t ^ ((0 : ℝ) / 2) = 1 := by simp
  rw [hden, div_one, LeviCivitaData.curvatureDerivativeNorm_zero]
  linarith

private theorem local_curvatureDerivative_bound_of_initial_zero_core (n l : ℕ) (K α r : ℝ)
    (hK : 0 < K) (hα : 0 < α) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
        [T2Space N] [SecondCountableTopology N],
      ∀ (T : ℝ), 0 < T → T ≤ α / K →
      ∀ (F : RicciFlow n N (Set.Icc 0 T)) (p : N),
        IsCompact (closure ((F.metric 0).ball p r)) →
        (∀ t ∈ Set.Icc 0 T, ∀ x : N, (F.connection t).curvatureTensorNorm x ≤ K) →
        (∀ j ≤ l, ∀ x : N, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
        ∀ t ∈ Set.Icc 0 T, (0 < t ∨ 0 ≤ l) →
        ∀ x ∈ (F.metric 0).ball p (r / 2),
          (F.connection t).curvatureDerivativeNorm 0 x ≤
            C / t ^ (((0 - l : ℕ) : ℝ) / 2) := by
  refine ⟨K + 1, by linarith, ?_⟩
  intro N _ _ _ _ _ T hT hTK F p hcompact hRm hinit t ht hbranch x hx
  have hcurv := hRm t ht x
  have hden : t ^ (((0 - l : ℕ) : ℝ) / 2) = 1 := by simp
  rw [hden, div_one, LeviCivitaData.curvatureDerivativeNorm_zero]
  linarith

private theorem shi_half_window_rescale
    {theta s A B : ℝ} {e : ℕ}
    (htheta : 0 < theta) (hs : theta / 2 ≤ s) (hB : 0 ≤ B)
    (hprev : B ≤ A / s ^ ((e : ℝ) / 2)) :
    (Real.sqrt theta) ^ e * B ≤ (Real.sqrt 2) ^ e * A := by
  have hspos : 0 < s := (half_pos htheta).trans_le hs
  have hsqrt : Real.sqrt theta ≤ Real.sqrt 2 * Real.sqrt s := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith only [hs])
  have hpow :
      (Real.sqrt theta) ^ e ≤ (Real.sqrt 2) ^ e * (Real.sqrt s) ^ e := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (Real.sqrt_nonneg theta) hsqrt e
  have hden : 0 < (Real.sqrt s) ^ e := pow_pos (Real.sqrt_pos.mpr hspos) e
  have hprevious : B * (Real.sqrt s) ^ e ≤ A := by
    apply (le_div_iff₀ hden).mp
    simpa only [Real.rpow_div_two_eq_sqrt _ hspos.le, Real.rpow_natCast] using hprev
  calc
    (Real.sqrt theta) ^ e * B ≤ ((Real.sqrt 2) ^ e * (Real.sqrt s) ^ e) * B :=
      mul_le_mul_of_nonneg_right hpow hB
    _ = (Real.sqrt 2) ^ e * (B * (Real.sqrt s) ^ e) := by ring
    _ ≤ (Real.sqrt 2) ^ e * A :=
      mul_le_mul_of_nonneg_left hprevious (pow_nonneg (Real.sqrt_nonneg 2) e)

set_option maxHeartbeats 2000000 in

private theorem shi_local_prefix_bound (n k l : ℕ) (K alpha r : ℝ)
    (hK : 0 < K) (halpha : 0 < alpha) (hr : 0 < r) (hk : k ≠ 0) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
        [IsManifold (𝓡 n) ∞ N] [T2Space N] [SecondCountableTopology N],
      ∀ (T : ℝ), 0 < T → T ≤ alpha / K →
      ∀ (F : RicciFlow n N (Icc 0 T)) (p : N),
        IsCompact (closure ((F.metric 0).ball p r)) →
        (∀ t ∈ Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        (∀ j ≤ l, ∀ x ∈ (F.metric 0).ball p r,
          (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
        ∀ t ∈ Icc 0 T, (0 < t ∨ k ≤ l) →
        ∀ x ∈ (F.metric 0).ball p (r / 2),
          (F.connection t).curvatureDerivativeNorm k x ≤
            A / t ^ (((k - l : ℕ) : ℝ) / 2) := by
  classical
  let delta : ℝ := r / (2 * (k : ℝ))
  let R : ℕ → ℝ := fun j => r - (j : ℝ) * delta
  let Theta : ℝ := alpha / K
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hdelta : 0 < delta := div_pos hr (mul_pos (by norm_num) hkpos)
  have hbudget : (k : ℝ) * delta = r / 2 := by
    dsimp only [delta]
    field_simp [hkpos.ne']
  have hRzero : R 0 = r := by simp only [R, Nat.cast_zero, zero_mul, sub_zero]
  have hRfinal : R k = r / 2 := by
    dsimp only [R]
    rw [hbudget]
    ring
  have hRsucc (m : ℕ) : R (m + 1) + delta = R m := by
    dsimp only [R]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hRanti {i j : ℕ} (hij : i ≤ j) : R j ≤ R i := by
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp only [R]
    linarith only [mul_le_mul_of_nonneg_right hc hdelta.le]
  have hmargin (m : ℕ) : R (m + 1) + delta ≤ r := by
    rw [hRsucc m]
    simpa only [hRzero] using hRanti (Nat.zero_le m)
  obtain ⟨L, G, hL, hG, hcutoff⟩ :=
    M04.exists_shi_geometric_cutoff n K alpha delta hK hdelta
  have hgeometry (m : ℕ) :
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
        [IsManifold (𝓡 n) ∞ N] [T2Space N],
      ∀ (T : ℝ), 0 < T → T ≤ alpha / K →
      ∀ (F : RicciFlow n N (Icc 0 T)) (p : N),
        IsCompact (closure ((F.metric 0).ball p r)) →
        (∀ t ∈ Icc 0 T, ∀ y ∈ (F.metric 0).ball p r,
          (F.connection t).curvatureTensorNorm y ≤ K) →
        ∀ x ∈ (F.metric 0).ball p (R (m + 1)),
        ∃ C : Set N, IsCompact C ∧
          (∀ i ≤ m, C ⊆ (F.metric 0).ball p (R i)) ∧
          x ∈ C ∧ ∃ eta : ℝ → N → ℝ,
          ContinuousOn (Function.uncurry eta) (Icc 0 T ×ˢ C) ∧
          (∀ t ∈ Icc 0 T, ∀ y ∈ C, 0 ≤ eta t y) ∧
          (∀ t ∈ Icc 0 T, ∀ y ∈ C, eta t y ≤ 1) ∧
          (∀ t ∈ Icc 0 T, ∀ y ∈ C \ interior C, eta t y = 0) ∧
          (∀ t ∈ Icc 0 T, eta t x = 1) ∧
          M04.shiPhysicalCutoffSupports F.metric F.connection T C eta L G := by
    intro N _ _ _ _ T hT hTK F p hcompact hRm x hx
    obtain ⟨Rc, hRcpos, hRcupper, hC, hCball, hflow⟩ :=
      M04.exists_compact_recentered_carrier_for_flow_balls F hK hr hdelta
        hT.le hTK p x hcompact hRm hx (hmargin m)
    let C : Set N := {y | (F.metric 0).edist x y ≤ ENNReal.ofReal Rc}
    have hCindex : ∀ i ≤ m, C ⊆ (F.metric 0).ball p (R i) := by
      intro i him y hy
      have hrad : R (m + 1) + 3 * delta / 4 ≤ R i := by
        calc
          R (m + 1) + 3 * delta / 4 ≤ R m := by
            linarith only [hRsucc m, hdelta]
          _ ≤ R i := hRanti him
      have hyball := hCball hy
      change (F.metric 0).edist p y <
        ENNReal.ofReal (R (m + 1) + 3 * delta / 4) at hyball
      change (F.metric 0).edist p y < ENNReal.ofReal (R i)
      exact hyball.trans_le (ENNReal.ofReal_le_ofReal hrad)
    have hCouter : C ⊆ (F.metric 0).ball p r := by
      simpa only [hRzero] using hCindex 0 (Nat.zero_le m)
    have hRmC : ∀ t ∈ Icc 0 T, ∀ y ∈ C,
        (F.connection t).curvatureTensorNorm y ≤ K := by
      intro t ht y hy
      exact hRm t ht y (hCouter hy)
    have hretained : ∀ t ∈ Icc 0 T,
        closure ((F.metric t).ball x (M04.shiRetainedFlowRadius n alpha delta)) ⊆ C := by
      simpa only [M04.shiRetainedFlowRadius] using hflow
    obtain ⟨hxC, eta, heta, heta0, heta1, hboundary, hcenter, hsupport⟩ :=
      hcutoff N T hT.le hTK F x C hC hretained hRmC
    exact ⟨C, hC, hCindex, hxC, eta, heta, heta0, heta1, hboundary, hcenter, hsupport⟩
  let P : ℕ → ℝ → Prop := fun j A =>
    ∀ (N : Type u) [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
      [IsManifold (𝓡 n) ∞ N] [T2Space N] [SecondCountableTopology N],
    ∀ (T : ℝ), 0 < T → T ≤ alpha / K →
    ∀ (F : RicciFlow n N (Icc 0 T)) (p : N),
      IsCompact (closure ((F.metric 0).ball p r)) →
      (∀ t ∈ Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
        (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ i ≤ l, ∀ x ∈ (F.metric 0).ball p r,
        (F.connection 0).curvatureDerivativeNorm i x ≤ K) →
      ∀ t ∈ Icc 0 T, (0 < t ∨ j ≤ l) →
      ∀ x ∈ (F.metric 0).ball p (R j),
        (F.connection t).curvatureDerivativeNorm j x ≤
          A / t ^ (((j - l : ℕ) : ℝ) / 2)
  have hInd : ∀ j, j ≤ k → ∃ A : ℝ, 0 < A ∧ P j A := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hjk
      cases j with
      | zero =>
        refine ⟨K + 1, by linarith, ?_⟩
        intro N _ _ _ _ _ T hT hTK F p hcompact hRm hinit t ht hbranch x hx
        have hxouter : x ∈ (F.metric 0).ball p r := by simpa only [hRzero] using hx
        have hcurv := hRm t ht x hxouter
        rw [Nat.zero_sub, Nat.cast_zero, zero_div, Real.rpow_zero,
          div_one, LeviCivitaData.curvatureDerivativeNorm_zero]
        linarith only [hcurv]
      | succ m =>
        have hprev (i : Fin (m + 1)) : ∃ A : ℝ, 0 < A ∧ P (i : ℕ) A :=
          ih (i : ℕ) i.isLt (by omega)
        choose A hA hAll using hprev
        let H : ℝ := 1 + ∑ i : Fin (m + 1), (Real.sqrt 2) ^ ((i : ℕ) - l) * A i
        have hterm (i : Fin (m + 1)) : 0 ≤ (Real.sqrt 2) ^ ((i : ℕ) - l) * A i :=
          mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) _) (hA i).le
        have hsum0 : 0 ≤ ∑ i : Fin (m + 1), (Real.sqrt 2) ^ ((i : ℕ) - l) * A i :=
          Finset.sum_nonneg (fun i _ => hterm i)
        have hHpos : 0 < H := by dsimp only [H]; linarith only [hsum0]
        have hHi (i : Fin (m + 1)) : (Real.sqrt 2) ^ ((i : ℕ) - l) * A i ≤ H := by
          have hi : (Real.sqrt 2) ^ ((i : ℕ) - l) * A i ≤
              ∑ j : Fin (m + 1), (Real.sqrt 2) ^ ((j : ℕ) - l) * A j :=
            Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
          dsimp only [H]
          linarith only [hi]
        by_cases hlow : m + 1 ≤ l
        · let U : ℝ := max ((9 * H ^ 2 + 1) * K ^ 2)
            (M04.shiCutoffThreshold (M04.shiLocalBernsteinCoefficient H)
              (M04.shiLocalBernsteinRemainder n m (max 1 Theta) H) L G (1 + Theta))
          refine ⟨1 + Real.sqrt U, by positivity, ?_⟩
          intro N _ _ _ _ _ T hT hTK F p hcompact hRm hinit t ht hbranch x hx
          obtain ⟨C, hC, hCindex, hxC, eta, heta, heta0, heta1,
              hboundary, hcenter, hsupport⟩ :=
            hgeometry m N T hT hTK F p hcompact hRm x hx
          have hCouter : C ⊆ (F.metric 0).ball p r := by
            simpa only [hRzero] using hCindex 0 (Nat.zero_le m)
          have hbound : ∀ i ≤ m, ∀ s ∈ Icc 0 T, ∀ y ∈ C,
              (F.connection s).curvatureDerivativeNorm i y ≤ H := by
            intro i him s hs y hy
            let ii : Fin (m + 1) := ⟨i, Nat.lt_succ_of_le him⟩
            have hil : i ≤ l := by omega
            have hp := hAll ii N T hT hTK F p hcompact hRm hinit s hs
              (Or.inr hil) y (hCindex i him hy)
            have hp' : (F.connection s).curvatureDerivativeNorm i y ≤ A ii := by
              simpa only [ii, Nat.sub_eq_zero_of_le hil, Nat.cast_zero,
                zero_div, Real.rpow_zero, div_one] using hp
            have hAi : A ii ≤ H := by
              simpa only [ii, Nat.sub_eq_zero_of_le hil, pow_zero, one_mul] using hHi ii
            exact hp'.trans hAi
          have hinitC : ∀ y ∈ C,
              (F.connection 0).curvatureDerivativeNorm (m + 1) y ≤ K := by
            intro y hy
            exact hinit (m + 1) hlow y (hCouter hy)
          have hresult := M04.shi_initial_local_step F hC m
            (Θ := Theta) hT hTK hHpos.le hK.le hL hG eta
            heta heta0 heta1 hboundary hsupport hbound hinitC ht hxC (hcenter t ht)
          simpa only [U, Nat.sub_eq_zero_of_le hlow, Nat.cast_zero,
            zero_div, Real.rpow_zero, div_one] using hresult
        · have hlm : l ≤ m := by omega
          let U : ℝ := M04.shiCutoffThreshold (M04.shiLocalBernsteinCoefficient H)
            (M04.shiLocalBernsteinRemainder n m (M04.shiShiftedReactionScale l Theta) H)
            (Theta * L) (Theta * G) (1 / 2)
          refine ⟨1 + Real.sqrt (2 * U), by positivity, ?_⟩
          intro N _ _ _ _ _ T hT hTK F p hcompact hRm hinit theta ht hbranch x hx
          have htheta : 0 < theta := hbranch.resolve_right hlow
          obtain ⟨C, hC, hCindex, hxC, eta, heta, heta0, heta1,
              hboundary, hcenter, hsupport⟩ :=
            hgeometry m N T hT hTK F p hcompact hRm x hx
          have hbound : ∀ i ≤ m, ∀ s ∈ Icc (theta / 2) theta, ∀ y ∈ C,
              (Real.sqrt theta) ^ (i - l) *
                (F.connection s).curvatureDerivativeNorm i y ≤ H := by
            intro i him s hs y hy
            let ii : Fin (m + 1) := ⟨i, Nat.lt_succ_of_le him⟩
            have hspos : 0 < s := (half_pos htheta).trans_le hs.1
            have hsT : s ∈ Icc 0 T := ⟨hspos.le, hs.2.trans ht.2⟩
            have hp := hAll ii N T hT hTK F p hcompact hRm hinit s hsT
              (Or.inl hspos) y (hCindex i him hy)
            have hN : 0 ≤ (F.connection s).curvatureDerivativeNorm i y := Real.sqrt_nonneg _
            exact (shi_half_window_rescale htheta hs.1 hN hp).trans (hHi ii)
          have hresult := M04.shi_shifted_local_step F hC hlm
            (Θ := Theta) htheta ht.2 (ht.2.trans hTK) hHpos.le hL hG eta
            heta heta0 heta1 hboundary hsupport hbound hxC (hcenter theta ht)
          simpa only [U] using hresult
  simpa only [P, hRfinal] using hInd k le_rfl


theorem local_curvatureDerivative_bound (n k : ℕ) (K α r : ℝ)
    (hK : 0 < K) (hα : 0 < α) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
        [T2Space N] [SecondCountableTopology N],
      ∀ (T : ℝ), 0 < T → T ≤ α / K →
      ∀ (F : RicciFlow n N (Set.Icc 0 T)) (p : N),
        IsCompact (closure ((F.metric 0).ball p r)) →
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ (F.metric 0).ball p (r / 2),
          (F.connection t).curvatureDerivativeNorm k x ≤ C / t ^ ((k : ℝ) / 2) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro N _ _ _ _ _ T hT hTK F p hcompact hRm t ht x hx
    rw [curvatureDerivativeNorm_zero_dim (F.metric t) (F.connection t) k x]
    exact (div_nonneg (by norm_num)
      (Real.rpow_nonneg ht.1.le ((k : ℝ) / 2)))
  by_cases hk : k = 0
  · subst k
    simpa using local_curvatureDerivative_bound_zero_core n K α r hK hα hr
  obtain ⟨A, hA, hcore⟩ := shi_local_prefix_bound n k 0 K α r hK hα hr hk
  refine ⟨A, hA, ?_⟩
  intro N _ _ _ _ _ T hT hTK F p hcompact hRm t ht x hx
  have hinit : ∀ j ≤ (0 : ℕ), ∀ y ∈ (F.metric 0).ball p r,
      (F.connection 0).curvatureDerivativeNorm j y ≤ K := by
    intro j hj y hy
    have hj0 : j = 0 := by omega
    subst j
    rw [LeviCivitaData.curvatureDerivativeNorm_zero]
    exact hRm 0 ⟨le_rfl, hT.le⟩ y hy
  simpa only [Nat.sub_zero] using
    hcore N T hT hTK F p hcompact hRm hinit t ⟨ht.1.le, ht.2⟩ (Or.inl ht.1) x hx


theorem local_curvatureDerivative_bound_of_initial (n k l : ℕ) (K α r : ℝ)
    (hK : 0 < K) (hα : 0 < α) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
        [T2Space N] [SecondCountableTopology N],
      ∀ (T : ℝ), 0 < T → T ≤ α / K →
      ∀ (F : RicciFlow n N (Set.Icc 0 T)) (p : N),
        IsCompact (closure ((F.metric 0).ball p r)) →
        (∀ t ∈ Set.Icc 0 T, ∀ x : N, (F.connection t).curvatureTensorNorm x ≤ K) →
        (∀ j ≤ l, ∀ x : N, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
        ∀ t ∈ Set.Icc 0 T, (0 < t ∨ k ≤ l) →
        ∀ x ∈ (F.metric 0).ball p (r / 2),
          (F.connection t).curvatureDerivativeNorm k x ≤ C / t ^ (((k - l : ℕ) : ℝ) / 2) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro N _ _ _ _ _ T hT hTK F p hcompact hRm hinit t ht hbranch x hx
    rw [curvatureDerivativeNorm_zero_dim (F.metric t) (F.connection t) k x]
    exact (div_nonneg (by norm_num)
      (Real.rpow_nonneg ht.1 (((k - l : ℕ) : ℝ) / 2)))
  by_cases hk : k = 0
  · subst k
    exact local_curvatureDerivative_bound_of_initial_zero_core n l K α r hK hα hr
  obtain ⟨A, hA, hcore⟩ := shi_local_prefix_bound n k l K α r hK hα hr hk
  refine ⟨A, hA, ?_⟩
  intro N _ _ _ _ _ T hT hTK F p hcompact hRm hinit t ht hbranch x hx
  exact hcore N T hT hTK F p hcompact
    (fun s hs y _ => hRm s hs y) (fun j hj y _ => hinit j hj y) t ht hbranch x hx

end PoincareConjecture

