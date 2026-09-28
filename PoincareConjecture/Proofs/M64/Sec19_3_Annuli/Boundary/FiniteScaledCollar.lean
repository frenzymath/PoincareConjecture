import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteFrameCollar
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ConnectionContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ScaledBoundarySubdivision
import PoincareConjecture.Proofs.M64.Mathlib.ScaledIntervalIntegrability

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators

namespace PoincareConjecture.M64

open M65Gauss M65StrictTrace

set_option maxHeartbeats 1600000 in

theorem finite_scaled_boundary_collar_limit {n : ℕ} {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (g : Bool → ℝ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (D : ∀ u x, LeviCivitaData (g u x)) (H : Bool → ℝ → ℂ → EuclideanSpace ℝ (Fin n))
    (V : Bool → ℝ → ℂ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (R e C : Bool → ℝ → ℝ) (B : Bool → ℝ → ℝ) (L : Bool → ℝ → ℝ → ℝ)
    (he : ∀ u x, 0 < e u x) (heR : ∀ u x, 2 * e u x < R u x)
    (hR1 : ∀ u x, R u x < 1) (hC : ∀ u x, 0 ≤ C u x)
    (hH : ∀ u x, ContDiffOn ℝ 1 (H u x)
      (closedBall (0 : ℂ) (R u x) ∩ {z | 0 ≤ z.im}))
    (hV : ∀ u x, ContinuousOn (V u x)
      (closedBall (0 : ℂ) (R u x) ∩ {z | 0 ≤ z.im}))
    (hVi : ∀ u x, ContDiffOn ℝ 1 (V u x)
      (ball (0 : ℂ) (R u x) ∩ {z | 0 < z.im}))
    (hDV : ∀ u x, MemLp (fun z => fderiv ℝ (V u x) z 1)
      2 (volume.restrict (ball (0 : ℂ) (R u x) ∩ {z | 0 < z.im})))
    (hholder : ∀ u x, ∀ z ∈ closedBall (0 : ℂ) (R u x) ∩ {z | 0 ≤ z.im},
      ∀ w ∈ closedBall (0 : ℂ) (R u x) ∩ {z | 0 ≤ z.im},
        ‖V u x z - V u x w‖ ≤ C u x * Real.sqrt ‖z - w‖)
    (hinside : ∀ u x, ∀ z ∈ ball (0 : ℂ) (R u x) ∩ {z | 0 < z.im},
      (g u x).inner (H u x z)
        (covariantDerivativeAlongMap (D u x) (H u x) (fun w => (V u x w).1) z 1)
        (V u x z).2 = L u z.im (x + r * z.re))
    (hboundary : ∀ u x, ∀ t ∈ Icc (-(e u x)) (e u x),
      ContDiffAt ℝ 1 (fun s : ℝ => (V u x (s : ℂ)).1) t ∧
      (g u x).inner (H u x (t : ℂ))
        (deriv (fun s : ℝ => (V u x (s : ℂ)).1) t +
          connectionCoefficient (D u x) (H u x (t : ℂ))
            (fderivWithin ℝ (H u x)
              (closedBall (0 : ℂ) (R u x) ∩ {z | 0 ≤ z.im}) (t : ℂ) 1)
              (V u x (t : ℂ)).1) (V u x (t : ℂ)).2 = B u (x + r * t)) :
    (∀ u, IntervalIntegrable (B u) volume 0 p) ∧
      ∃ h : ℕ → ℝ, (∀ k, h k ∈ Ioo (0 : ℝ) (1 / 2)) ∧ Tendsto h atTop (𝓝 0) ∧
        (∀ u k, IntervalIntegrable (L u (h k)) volume 0 p) ∧
        ∀ u, Tendsto (fun k => ∫ theta in (0 : ℝ)..p, L u (h k) theta) atTop
          (𝓝 (∫ theta in (0 : ℝ)..p, B u theta)) := by
  classical
  let width := fun x => min (e false x) (e true x)
  have hwidth (x : ℝ) : 0 < width x := lt_min (he false x) (he true x)
  have hwidthle (u : Bool) (x : ℝ) : width x ≤ e u x := by
    cases u
    · exact min_le_left _ _
    · exact min_le_right _ _
  obtain ⟨N, hN, tag, htag⟩ := exists_subordinate_scaled_subdivision hp hr width hwidth
  let v := fun k : ℕ => p * (k : ℝ) / N
  let a := fun i : Fin N => (v i - tag i) / r
  let b := fun i : Fin N => (v (i.val + 1) - tag i) / r
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hv0 : v 0 = 0 := by simp only [v, Nat.cast_zero, mul_zero, zero_div]
  have hvN : v N = p := by simp only [v, mul_div_cancel_right₀ _ hNR.ne']
  have hvmono (k : ℕ) : v k ≤ v (k + 1) := by
    dsimp only [v]
    apply div_le_div_of_nonneg_right _ hNR.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k) hp.le
  have hab (i : Fin N) : a i ≤ b i :=
    div_le_div_of_nonneg_right (sub_le_sub_right (hvmono i) _) hr.le
  have hcell (u : Bool) (i : Fin N) : Icc (a i) (b i) ⊆ Icc (-(e u (tag i))) (e u (tag i)) := by
    have hh : Icc (a i) (b i) ⊆ Icc (-(width (tag i))) (width (tag i)) := by
      simpa only [a, b, v, sub_zero, zero_add, Nat.cast_add, Nat.cast_one] using htag i
    exact hh.trans (Icc_subset_Icc (neg_le_neg (hwidthle u (tag i))) (hwidthle u (tag i)))
  let K := fun u x => closedBall (0 : ℂ) (R u x) ∩ {z | 0 ≤ z.im}
  let W := fun u x => ball (0 : ℂ) (R u x) ∩ {z | 0 < z.im}
  have hR (u : Bool) (x : ℝ) : 0 < R u x := by linarith [he u x, heR u x]
  have hWK (u : Bool) (x : ℝ) : W u x ⊆ K u x := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  obtain ⟨delta, hdelta, hde, h, hh, hlim, hconnection⟩ := finite_halfDisk_frame_collar_limit
    (fun j : Bool × Fin N => g j.1 (tag j.2)) (fun j => D j.1 (tag j.2))
    (fun j => H j.1 (tag j.2)) (fun j => V j.1 (tag j.2)) (fun _ _ => r)
    (fun j => R j.1 (tag j.2)) (fun j => e j.1 (tag j.2)) (fun j => C j.1 (tag j.2))
    (fun j => a j.2) (fun j => b j.2) (fun j => he j.1 (tag j.2))
    (fun j => heR j.1 (tag j.2)) (fun j => hC j.1 (tag j.2))
    (fun j => hab j.2) (fun j => hcell j.1 j.2) (fun j => hH j.1 (tag j.2))
    (fun _ => contDiffOn_const) (fun j => hV j.1 (tag j.2)) (fun j => hVi j.1 (tag j.2))
    (fun j => hDV j.1 (tag j.2))
    (fun j t ht => (hboundary j.1 (tag j.2) t ht).1) (fun j => hholder j.1 (tag j.2))
  have hdhalf : delta < 1 / 2 := by
    have hd := hde (false, ⟨0, hN⟩)
    have he' := heR false (tag ⟨0, hN⟩)
    have hR' := hR1 false (tag ⟨0, hN⟩)
    linarith
  let J := fun (u : Bool) (i : Fin N) (h t : ℝ) =>
    let z := (t : ℂ) + (h : ℂ) * I
    (g u (tag i)).inner (H u (tag i) z)
      (covariantDerivativeAlongMap (D u (tag i)) (H u (tag i))
        (fun w => (V u (tag i) w).1) z 1) (V u (tag i) z).2
  let J0 := fun (u : Bool) (i : Fin N) (t : ℝ) =>
    (g u (tag i)).inner (H u (tag i) (t : ℂ))
      (deriv (fun s : ℝ => (V u (tag i) (s : ℂ)).1) t +
        connectionCoefficient (D u (tag i)) (H u (tag i) (t : ℂ))
          (fderivWithin ℝ (H u (tag i)) (K u (tag i)) (t : ℂ) 1)
          (V u (tag i) (t : ℂ)).1) (V u (tag i) (t : ℂ)).2
  have hrect (u : Bool) (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) (k : ℕ) :
      (t : ℂ) + (h k : ℂ) * I ∈ W u (tag i) := by
    refine ⟨mem_ball_zero_iff.mpr (collar_rectangle_norm_lt (heR u (tag i)) (hcell u i ht)
      ⟨(hh k).1.le, ((hh k).2.trans (hde (u, i))).le⟩), ?_⟩
    simpa using (hh k).1
  have hJ (u : Bool) (i : Fin N) (k : ℕ) :
      ContinuousOn (J u i (h k)) (Icc (a i) (b i)) :=
    (frame_connection_continuousOn (D u (tag i)) (halfDisk_differential_domain (hR u (tag i))).1
      ((hH u (tag i)).mono (hWK u (tag i))) (hVi u (tag i)).fst
      ((hV u (tag i)).snd.mono (hWK u (tag i)))).comp
        (continuous_ofReal.add continuous_const).continuousOn (fun t ht => hrect u i t ht k)
  have hJ0 (u : Bool) (i : Fin N) : ContinuousOn (J0 u i) (Icc (a i) (b i)) :=
    (halfDisk_boundary_connection_continuousOn (D u (tag i)) (hR u (tag i))
      (by linarith [he u (tag i), heR u (tag i)]) (hH u (tag i)) (hV u (tag i))
      (fun t ht => (hboundary u (tag i) t ht).1)).mono (hcell u i)
  have hJvalue (u : Bool) (i : Fin N) (k : ℕ) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      J u i (h k) t = L u (h k) (tag i + r * t) := by
    simpa only [J, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, zero_mul, add_zero, zero_add, add_re, mul_re, mul_zero, sub_zero] using
        hinside u (tag i) _ (hrect u i t ht k)
  have hJ0value (u : Bool) (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      J0 u i t = B u (tag i + r * t) := (hboundary u (tag i) t (hcell u i ht)).2
  have hBL (u : Bool) (i : Fin N) : IntervalIntegrable (B u) volume (v i) (v (i.val + 1)) :=
    intervalIntegrable_of_scaled_coordinates (hvmono i) hr (hJ0 u i) (hJ0value u i)
  have hLL (u : Bool) (i : Fin N) (k : ℕ) :
      IntervalIntegrable (L u (h k)) volume (v i) (v (i.val + 1)) :=
    intervalIntegrable_of_scaled_coordinates (hvmono i) hr (hJ u i k) (hJvalue u i k)
  have hJlimit (u : Bool) (i : Fin N) :
      Tendsto (fun k => ∫ t in (a i)..(b i), r * L u (h k) (tag i + r * t)) atTop
        (𝓝 (∫ t in (a i)..(b i), r * B u (tag i + r * t))) := by
    have hj : Tendsto (fun k => ∫ t in (a i)..(b i), r * J u i (h k) t) atTop
      (𝓝 (∫ t in (a i)..(b i), r * J0 u i t)) := hconnection (u, i)
    have hrewrite (k : ℕ) : (∫ t in (a i)..(b i), r * J u i (h k) t) =
        ∫ t in (a i)..(b i), r * L u (h k) (tag i + r * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg (fun z : ℝ => r * z)
        (hJvalue u i k t (by simpa only [uIcc_of_le (hab i)] using ht))
    have hrewrite0 : (∫ t in (a i)..(b i), r * J0 u i t) =
        ∫ t in (a i)..(b i), r * B u (tag i + r * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg (fun z : ℝ => r * z)
        (hJ0value u i t (by simpa only [uIcc_of_le (hab i)] using ht))
    simpa only [hrewrite, hrewrite0] using hj
  have hsumB (u : Bool) : (∑ i : Fin N, ∫ t in (a i)..(b i), r * B u (tag i + r * t)) =
      ∫ t in (0 : ℝ)..p, B u t := by
    simpa only [hv0, hvN] using scaled_subdivision_integral v tag hr.ne' (B u)
      (fun k hk => hBL u ⟨k, hk⟩)
  have hsumL (u : Bool) (k : ℕ) :
      (∑ i : Fin N, ∫ t in (a i)..(b i), r * L u (h k) (tag i + r * t)) =
        ∫ t in (0 : ℝ)..p, L u (h k) t := by
    simpa only [hv0, hvN] using scaled_subdivision_integral v tag hr.ne' (L u (h k))
      (fun j hj => hLL u ⟨j, hj⟩ k)
  refine ⟨?_, h, fun k => ⟨(hh k).1, (hh k).2.trans hdhalf⟩, hlim, ?_, ?_⟩
  · intro u
    simpa only [hv0, hvN] using intervalIntegrable_of_grid v (B u)
      (fun k hk => hBL u ⟨k, hk⟩)
  · intro u k
    simpa only [hv0, hvN] using intervalIntegrable_of_grid v (L u (h k))
      (fun j hj => hLL u ⟨j, hj⟩ k)
  · intro u
    have hs := tendsto_finsetSum Finset.univ (fun i _ => hJlimit u i)
    simpa only [hsumB, hsumL] using hs

end PoincareConjecture.M64
