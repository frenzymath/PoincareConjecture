import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakClassCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingQuadraticLiminf

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64ObservedWeakAnnulus_energy_le_liminf
    {e : M → E} (hei : IsEmbedding e) {c0 c1 : ℝ → M}
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    (A : ℕ → M64ObservedWeakAnnulus (n := n) e c0 c1)
    (L : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {C : ℝ} (hC : ∀ j i, ‖(A j).column i‖ ^ 2 ≤ C)
    (hweak : ∀ i, WeakConverges (fun j => (A j).column i) (L.column i))
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A j).map p) atTop (𝓝 (L.map p))) :
    L.energy B ≤ liminf (fun j => (A j).energy B) atTop := by
  let H : M → E →L[ℝ] E →L[ℝ] ℝ := fun q => (1 / 2 : ℝ) • B q
  have hH : Continuous H := (continuous_const (y := (1 / 2 : ℝ))).smul hB
  have hscale (q : M) : ‖H q‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro w
    change ‖(1 / 2 : ℝ) • B q w‖ ≤ K * ‖w‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hh := (B q).le_opNorm w
    have hs := mul_le_mul_of_nonneg_right (hb q) (norm_nonneg w)
    have hn := mul_nonneg hK (norm_nonneg w)
    linarith
  let Q := fun j p => H ((A j).map p)
  let Q0 := fun p => H (L.map p)
  let q := fun j i => ∫ p in S, Q j p ((A j).column i p) ((A j).column i p)
  have hQ (j : ℕ) : AEStronglyMeasurable (Q j) mu :=
    hH.comp_aestronglyMeasurable ((A j).map_aestronglyMeasurable hei)
  have hQ0 : AEStronglyMeasurable Q0 mu :=
    hH.comp_aestronglyMeasurable (L.map_aestronglyMeasurable hei)
  have hQlim : ∀ᵐ p ∂mu, Tendsto (fun j => Q j p) atTop (𝓝 (Q0 p)) := by
    filter_upwards [hlim] with p hp
    exact (hH.tendsto _).comp hp
  have hC0 : 0 ≤ C := (sq_nonneg ‖(A 0).column 0‖).trans (hC 0 0)
  have hnorm (j : ℕ) (i : Fin 2) : ‖(A j).column i‖ ≤ Real.sqrt C := by
    nlinarith [Real.sq_sqrt hC0, Real.sqrt_nonneg C, norm_nonneg ((A j).column i), hC j i]
  have hcol (i : Fin 2) : (∫ p in S, Q0 p (L.column i p) (L.column i p)) ≤
      liminf (fun j => q j i) atTop := by
    exact m64MovingQuadratic_le_liminf Q Q0 hQ hQ0 hK
      (fun j => Eventually.of_forall fun p => hscale ((A j).map p)) hQlim
      (fun j => Eventually.of_forall fun p v => by
        change 0 ≤ (1 / 2 : ℝ) * B ((A j).map p) v v
        exact mul_nonneg (by norm_num) (hpos _ _))
      (fun j => Eventually.of_forall fun p v w => by
        change (1 / 2 : ℝ) * B ((A j).map p) v w = (1 / 2 : ℝ) * B ((A j).map p) w v
        rw [hsymm]) (hweak i) (fun j => hnorm j i)
  have hqint (j : ℕ) (i : Fin 2) :
      IntegrableOn (fun p => Q j p ((A j).column i p) ((A j).column i p)) S volume :=
    (A j).column_energy_integrable H hH hei hscale i
  have hq0int (i : Fin 2) :
      IntegrableOn (fun p => Q0 p (L.column i p) (L.column i p)) S volume :=
    L.column_energy_integrable H hH hei hscale i
  have hqnonneg (j : ℕ) (i : Fin 2) : 0 ≤ q j i := integral_nonneg fun p =>
    mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (hpos _ _)
  have hqbound (j : ℕ) (i : Fin 2) : q j i ≤ K * C := by
    have hi := (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable ((A j).column i))).mp (Lp.memLp ((A j).column i))
    calc
      _ ≤ ∫ p in S, K * ‖(A j).column i p‖ ^ 2 := by
        apply integral_mono_ae (hqint j i) (hi.const_mul K)
        exact Eventually.of_forall fun p => by
          have hop := (Q j p).le_opNorm₂ ((A j).column i p) ((A j).column i p)
          have hh := mul_le_mul_of_nonneg_right (hscale ((A j).map p))
            (sq_nonneg ‖(A j).column i p‖)
          rw [Real.norm_eq_abs] at hop
          change ‖Q j p‖ * ‖(A j).column i p‖ ^ 2 ≤ _ at hh
          nlinarith [le_abs_self (Q j p ((A j).column i p) ((A j).column i p))]
      _ = K * ‖(A j).column i‖ ^ 2 := by
        rw [integral_const_mul, ← LpFiniteCoordinatesNative.l2_norm_sq]
      _ ≤ K * C := mul_le_mul_of_nonneg_left (hC j i) hK
  have hsum (j : ℕ) : q j 0 + q j 1 = (A j).energy B := by
    rw [← integral_add (hqint j 0) (hqint j 1)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      dsimp only [Q, H]
      simp only [smul_apply, smul_eq_mul]
      ring
  have hlow (i : Fin 2) : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop (fun j => q j i) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun j => hqnonneg j i)
  have hupp (i : Fin 2) : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (fun j => q j i) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun j => hqbound j i)
  calc
    _ = (∫ p in S, Q0 p (L.column 0 p) (L.column 0 p)) +
        ∫ p in S, Q0 p (L.column 1 p) (L.column 1 p) := by
      rw [← integral_add (hq0int 0) (hq0int 1)]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only [Q0, H]
        simp only [smul_apply, smul_eq_mul]
        ring
    _ ≤ liminf (fun j => q j 0) atTop + liminf (fun j => q j 1) atTop :=
      add_le_add (hcol 0) (hcol 1)
    _ ≤ liminf (fun j => q j 0 + q j 1) atTop :=
      le_liminf_add (hlow 0) (hupp 0) (hlow 1) (hupp 1).isCoboundedUnder_ge
    _ = _ := by simp only [hsum]

end PoincareConjecture
