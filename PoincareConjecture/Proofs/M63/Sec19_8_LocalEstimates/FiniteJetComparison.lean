import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetSpatialCalculus
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicMaximumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63CurvatureJetSquared_bound_of_finite_dissipation [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (N : ℕ) {A B R H : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hcurv : ∀ s ∈ Ioo a b, s - a ≤ H →
      ∀ y, m63CurvatureJetSquared F c 0 s y ≤ R)
    (hdiss : ∀ i ≤ N, ∀ s ∈ Ioo a b, s - a ≤ H → ∀ y,
      deriv (fun r => m63CurvatureJetSquared F c i r y) s -
          m62ArcSecondDerivative F c s (m63CurvatureJetSquared F c i s) y ≤
        -m63CurvatureJetSquared F c (i + 1) s y +
          A * m63CurvatureJetSquared F c i s y + B / (s - a) ^ i) :
    let C := (N : ℝ) + 1 + A * H
    let D := A * C ^ N * R + B * ∑ i ∈ Finset.range (N + 1), C ^ (N - i)
    ∀ x t, t ∈ Ioo a b → t - a ≤ H →
      m63CurvatureJetSquared F c N t x ≤ (C ^ N * R + D * (t - a)) / (t - a) ^ N := by
  let C := (N : ℝ) + 1 + A * H
  let w : ℕ → ℝ := fun i => C ^ (N - i)
  let D := A * C ^ N * R + B * ∑ i ∈ Finset.range (N + 1), w i
  let q : ℕ → ℝ → ℝ → ℝ := fun i y s => m63CurvatureJetSquared F c i s y
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hw (i : ℕ) : 0 ≤ w i := pow_nonneg hC _
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (mul_nonneg (mul_nonneg hA (pow_nonneg hC _)) hR)
      (mul_nonneg hB (Finset.sum_nonneg (fun i _ => hw i)))
  have hq (i : ℕ) (y s : ℝ) : 0 ≤ q i y s :=
    ((F.metric s).toRiemannianMetric.toCore (c y s)).re_inner_nonneg _
  have hqSmooth (i : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (q i))
      (univ ×ˢ Ioo a b) := m63CurvatureJetSquared_joint_contDiff F c hc i
  have hqs (i : ℕ) (s : ℝ) (hs : s ∈ Ioo a b) : ContDiff ℝ ∞ (fun y => q i y s) :=
    (hqSmooth i).comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, hs⟩)
  have hvs (s : ℝ) (hs : s ∈ Ioo a b) :
      ContDiff ℝ ∞ (fun y => (curveSpeed F c s y)⁻¹) :=
    ((speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hs⟩)).inv
        (fun y => (speed_pos F c hc (Ioo_subset_Icc_self hs) y).ne')
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hqt (i : ℕ) (y s : ℝ) (hs : s ∈ Ioo a b) : DifferentiableAt ℝ (q i y) s :=
    (((hqSmooth i).contDiffAt (hopen.mem_nhds ⟨mem_univ y, hs⟩)).comp s
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change ∀ x t, t ∈ Ioo a b → t - a ≤ H →
    q N x t ≤ (C ^ N * R + D * (t - a)) / (t - a) ^ N
  intro x t ht hshort
  have hrestart (sigma : ℝ) (hsigma : sigma ∈ Ioo a t) :
      (t - sigma) ^ N * q N x t ≤ C ^ N * R + D * (t - sigma) := by
    let Q : ℝ → ℝ → ℝ := fun y s =>
      ∑ i ∈ Finset.range (N + 1), w i * ((s - sigma) ^ i * q i y s)
    let V : ℝ → ℝ → ℝ := fun y s =>
      ∑ i ∈ Finset.range (N + 1), w i *
        ((i : ℝ) * (s - sigma) ^ (i - 1) * q i y s +
          (s - sigma) ^ i * deriv (q i y) s)
    have hclosed (s : ℝ) (hs : s ∈ Icc sigma t) : s ∈ Ioo a b :=
      ⟨lt_of_lt_of_le hsigma.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hinner (s : ℝ) (hs : s ∈ Ioo sigma t) : s ∈ Ioo a b :=
      hclosed s (Ioo_subset_Icc_self hs)
    have htime (s : ℝ) (hs : s ∈ Icc sigma t) : s - a ≤ H := by
      linarith only [hs.2, hshort]
    have hQjoint : ContDiffOn ℝ ∞ (Function.uncurry Q) (univ ×ˢ Ioo a b) := by
      apply ContDiffOn.sum
      intro i _
      exact contDiffOn_const.mul
        (((contDiff_snd.sub contDiff_const).contDiffOn.pow i).mul (hqSmooth i))
    have hQs (s : ℝ) (hs : s ∈ Ioo a b) : ContDiff ℝ ∞ (fun y => Q y s) :=
      hQjoint.comp_contDiff (contDiff_id.prodMk contDiff_const)
        (fun _ => ⟨mem_univ _, hs⟩)
    have hQtime (y s : ℝ) (hs : s ∈ Ioo sigma t) : HasDerivAt (Q y) (V y s) s := by
      apply HasDerivAt.fun_sum
      intro i _
      simpa only [id_eq, mul_one] using!
        (((((hasDerivAt_id s).sub_const sigma).fun_pow i).fun_mul
          (hqt i y s (hinner s hs)).hasDerivAt).const_mul (w i))
    have hQspace (y s : ℝ) (hs : s ∈ Ioo a b) :
        m62ArcSecondDerivative F c s (fun z => Q z s) y =
          ∑ i ∈ Finset.range (N + 1), w i * (s - sigma) ^ i *
            m62ArcSecondDerivative F c s (fun z => q i z s) y := by
      have hqa (i : ℕ) : ContDiff ℝ ∞ (m62ArcDerivative F c s (fun z => q i z s)) :=
        (hvs s hs).mul (contDiff_infty_iff_deriv.mp (hqs i s hs)).2
      have hfirst (z : ℝ) : m62ArcDerivative F c s (fun u => Q u s) z =
          ∑ i ∈ Finset.range (N + 1), w i * (s - sigma) ^ i *
            m62ArcDerivative F c s (fun u => q i u s) z := by
        have hd : HasDerivAt (fun u => Q u s)
            (∑ i ∈ Finset.range (N + 1), w i *
              ((s - sigma) ^ i * deriv (fun u => q i u s) z)) z :=
          HasDerivAt.fun_sum fun i _ =>
            ((((hqs i s hs).differentiable (by simp) z).hasDerivAt.const_mul
              ((s - sigma) ^ i)).const_mul (w i))
        rw [m62ArcDerivative, hd.deriv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [m62ArcDerivative]
        ring
      have hd : HasDerivAt
          (fun z => ∑ i ∈ Finset.range (N + 1), w i * (s - sigma) ^ i *
            m62ArcDerivative F c s (fun u => q i u s) z)
          (∑ i ∈ Finset.range (N + 1), w i * (s - sigma) ^ i *
            deriv (m62ArcDerivative F c s (fun u => q i u s)) y) y :=
        HasDerivAt.fun_sum fun i _ =>
          ((hqa i).differentiable (by simp) y).hasDerivAt.const_mul _
      change m62ArcDerivative F c s
        (fun z => m62ArcDerivative F c s (fun u => Q u s) z) y = _
      rw [show (fun z => m62ArcDerivative F c s (fun u => Q u s) z) =
        (fun z => ∑ i ∈ Finset.range (N + 1), w i * (s - sigma) ^ i *
          m62ArcDerivative F c s (fun u => q i u s) z) from funext hfirst]
      rw [m62ArcDerivative, hd.deriv, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [m62ArcSecondDerivative, m62ArcDerivative]
      ring
    have hQpde (y s : ℝ) (hs : s ∈ Ioo sigma t) :
        V y s ≤ m62ArcSecondDerivative F c s (fun z => Q z s) y + D := by
      let delta := s - sigma
      let L : ℕ → ℝ := fun i => w i *
        ((i : ℝ) * delta ^ (i - 1) * q i y s + delta ^ i *
          (deriv (q i y) s - m62ArcSecondDerivative F c s (fun z => q i z s) y))
      let T : ℕ → ℝ := fun i => w i * delta ^ i * q (i + 1) y s
      have hdelta : 0 ≤ delta := sub_nonneg.mpr hs.1.le
      have hage : 0 < s - a := sub_pos.mpr (hinner s hs).1
      have hdeltaAge : delta ≤ s - a := by dsimp only [delta]; linarith only [hsigma.1]
      have hdeltaH : delta ≤ H := hdeltaAge.trans (htime s (Ioo_subset_Icc_self hs))
      have hTnon (i : ℕ) : 0 ≤ T i :=
        mul_nonneg (mul_nonneg (hw i) (pow_nonneg hdelta i)) (hq (i + 1) y s)
      have hforcing (i : ℕ) : delta ^ i * (B / (s - a) ^ i) ≤ B := by
        calc
          _ = (delta ^ i * B) / (s - a) ^ i := by ring
          _ ≤ B := (div_le_iff₀ (pow_pos hage i)).mpr (by
            have h := mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hdelta hdeltaAge i) hB
            simpa only [mul_comm] using h)
      have hterm (i : ℕ) (hi : i ≤ N) :
          L i ≤ w i * ((i : ℝ) * delta ^ (i - 1) * q i y s +
            delta ^ i * (-q (i + 1) y s + A * q i y s)) + w i * B := by
        have hraw := mul_le_mul_of_nonneg_left
          (add_le_add_left (mul_le_mul_of_nonneg_left
            (hdiss i hi s (hinner s hs) (htime s (Ioo_subset_Icc_self hs)) y)
            (pow_nonneg hdelta i)) ((i : ℝ) * delta ^ (i - 1) * q i y s)) (hw i)
        have hf := mul_le_mul_of_nonneg_left (hforcing i) (hw i)
        change w i * (delta ^ i *
          (deriv (q i y) s - m62ArcSecondDerivative F c s (fun z => q i z s) y) +
            (i : ℝ) * delta ^ (i - 1) * q i y s) ≤ _ at hraw
        dsimp only [L]
        nlinarith only [hraw, hf]
      have hbase : L 0 ≤ A * C ^ N * R + B * w 0 - T 0 := by
        have h0 := hterm 0 (Nat.zero_le N)
        have hqR := hcurv s (hinner s hs) (htime s (Ioo_subset_Icc_self hs)) y
        have hreaction := mul_le_mul_of_nonneg_left hqR
          (mul_nonneg hA (pow_nonneg hC N))
        simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul,
          w, Nat.sub_zero] at h0
        dsimp only [T, w]
        simp only [pow_zero, mul_one, Nat.sub_zero]
        change A * C ^ N * q 0 y s ≤ A * C ^ N * R at hreaction
        nlinarith only [h0, hreaction]
      have hstep (i : ℕ) (hi : i + 1 ≤ N) :
          L (i + 1) ≤ T i - T (i + 1) + B * w (i + 1) := by
        have hwstep : w i = C * w (i + 1) := by
          dsimp only [w]
          rw [show N - i = N - (i + 1) + 1 by omega, pow_succ]
          ring
        have hiR : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
        have hcoef : ((i + 1 : ℕ) : ℝ) + A * delta ≤ C := by
          have h := mul_le_mul_of_nonneg_left hdeltaH hA
          dsimp only [C]
          linarith only [hiR, h]
        have hreaction : w (i + 1) *
            (((i + 1 : ℕ) : ℝ) * delta ^ i * q (i + 1) y s +
              delta ^ (i + 1) * (A * q (i + 1) y s)) ≤ T i := by
          calc
            _ = (w (i + 1) * delta ^ i * q (i + 1) y s) *
                (((i + 1 : ℕ) : ℝ) + A * delta) := by rw [pow_succ]; ring
            _ ≤ (w (i + 1) * delta ^ i * q (i + 1) y s) * C :=
              mul_le_mul_of_nonneg_left hcoef
                (mul_nonneg (mul_nonneg (hw (i + 1)) (pow_nonneg hdelta i))
                  (hq (i + 1) y s))
            _ = T i := by dsimp only [T]; rw [hwstep]; ring
        have h := hterm (i + 1) hi
        simp only [Nat.add_sub_cancel] at h
        dsimp only [T] at *
        nlinarith only [h, hreaction]

      have hfinite : ∀ k ≤ N,
          ∑ i ∈ Finset.range (k + 1), L i ≤
            A * C ^ N * R + B * ∑ i ∈ Finset.range (k + 1), w i - T k := by
        intro k
        induction k with
        | zero =>
          intro _
          simpa only [Nat.zero_add, Finset.sum_range_one] using hbase
        | succ k ih =>
          intro hk
          have hprev := ih (Nat.le_trans (Nat.le_succ k) hk)
          have hnext := hstep k hk
          rw [Finset.sum_range_succ L (k + 1), Finset.sum_range_succ w (k + 1)]
          linarith only [hprev, hnext]
      have hidentity : V y s - m62ArcSecondDerivative F c s (fun z => Q z s) y =
          ∑ i ∈ Finset.range (N + 1), L i := by
        rw [hQspace y s (hinner s hs)]
        dsimp only [V]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [L, delta]
        ring
      have hbound := hfinite N le_rfl
      have hnon := hTnon N
      dsimp only [D]
      linarith only [hidentity, hbound, hnon]
    have hQinit (y : ℝ) : Q y sigma = C ^ N * q 0 y sigma := by
      dsimp only [Q]
      rw [Finset.sum_eq_single 0]
      · simp [w]
      · intro i _ hi
        simp [hi]
      · intro hi
        exact False.elim (hi (by simp))
    have hcompare := Poincare.Parabolic.periodic_le_affine_mul_exp_of_weighted_parabolic_le
      (F := Q) (V := V) (w := fun y s => (curveSpeed F c s y)⁻¹)
      (B := fun _ _ => 0) (p := curvePeriod) (K := 0) (d := D) (R := C ^ N * R)
      (by unfold curvePeriod; positivity) hsigma.2 (by norm_num) hD
      (hQjoint.continuousOn.mono (fun z hz => ⟨hz.1, hclosed z.2 hz.2⟩))
      (fun s hs y => by
        dsimp only [Q]
        apply Finset.sum_congr rfl
        intro i _
        have h := m63CurvatureJetSquared_periodic F c hc i (hclosed s hs) y
        change q i (y + curvePeriod) s = q i y s at h
        rw [h])
      hQtime
      (fun y s hs => (hvs s (hinner s hs)).differentiable (by simp) y)
      (fun y s hs => (contDiff_infty_iff_deriv.mp (hQs s (hinner s hs))).2.differentiable
        (by simp) y)
      (fun y s hs => by
        simp only [zero_mul, add_zero]
        change V y s ≤ m62ArcSecondDerivative F c s (fun z => Q z s) y + D
        exact hQpde y s hs)
      (fun y => by
        rw [hQinit]
        exact mul_le_mul_of_nonneg_left
          (hcurv sigma (hclosed sigma ⟨le_rfl, hsigma.2.le⟩)
            (htime sigma ⟨le_rfl, hsigma.2.le⟩) y) (pow_nonneg hC N))
    have h := hcompare x t ⟨hsigma.2.le, le_rfl⟩
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    have htop : w N * ((t - sigma) ^ N * q N x t) ≤ Q x t :=
      Finset.single_le_sum (fun i _ => mul_nonneg (hw i)
        (mul_nonneg (pow_nonneg (sub_nonneg.mpr hsigma.2.le) i) (hq i x t)))
        (Finset.mem_range.mpr (Nat.lt_succ_self N))
    simpa only [w, Nat.sub_self, pow_zero, one_mul] using htop.trans h
  have hevent : ∀ᶠ sigma in 𝓝[>] a,
      (t - sigma) ^ N * q N x t ≤ C ^ N * R + D * (t - sigma) := by
    filter_upwards [Ioo_mem_nhdsGT ht.1] with sigma hsigma
    exact hrestart sigma hsigma
  have hleft : Tendsto (fun sigma => (t - sigma) ^ N * q N x t) (𝓝[>] a)
      (𝓝 ((t - a) ^ N * q N x t)) :=
    (show Continuous (fun sigma : ℝ => (t - sigma) ^ N * q N x t) by
      fun_prop).continuousAt.tendsto |>.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun sigma => C ^ N * R + D * (t - sigma)) (𝓝[>] a)
      (𝓝 (C ^ N * R + D * (t - a))) :=
    (show Continuous (fun sigma : ℝ => C ^ N * R + D * (t - sigma)) by
      fun_prop).continuousAt.tendsto |>.mono_left nhdsWithin_le_nhds
  have hlimit := le_of_tendsto_of_tendsto hleft hright hevent
  exact (le_div_iff₀ (pow_pos (sub_pos.mpr ht.1) N)).mpr
    (by simpa only [mul_comm] using hlimit)

end PoincareConjecture
