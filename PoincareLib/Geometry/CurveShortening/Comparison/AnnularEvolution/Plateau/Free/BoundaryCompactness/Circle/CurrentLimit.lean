import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Moving.QuadraticLiminf

/-!
# Weak continuity of the actual planar circle current

For a circle observation `u`, the current is the literal determinant
`u 0 * v 1 - u 1 * v 0`. Strong L2 convergence of values pairs with
weak L2 convergence of columns, so this current retains its integral.
This is independent of any candidate phase lift or limit regularity.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT.M64

open Poincare.Analysis.Sobolev.WeakCompactness

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The actual oriented determinant current of two planar vectors. Source: Morgan-Tian Lemma
19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
def planarCircleCurrent (u v : E) : ℝ := u 0 * v 1 - u 1 * v 0

private def quarterTurn : E →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (1 : Fin 2) 1)).comp
      (EuclideanSpace.proj 0) -
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 2) 1)).comp
      (EuclideanSpace.proj 1)

private theorem quarterTurn_inner (u v : E) :
    inner ℝ (quarterTurn u) v = planarCircleCurrent u v := by
  simp [quarterTurn, planarCircleCurrent, inner_sub_left,
    EuclideanSpace.inner_single_left, real_inner_smul_left]

private theorem inner_tendsto_weak_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {u w : ℕ → H} {v z : H} (hu : WeakConverges u v) (hw : Tendsto w atTop (𝓝 z))
    {A : ℝ} (hA : ∀ j, ‖u j‖ ≤ A) :
    Tendsto (fun j => inner ℝ (w j) (u j)) atTop (𝓝 (inner ℝ z v)) := by
  have hzero : Tendsto (fun j => inner ℝ (w j - z) (u j)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm (fun j => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hA j) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, zero_mul] using ((hw.sub_const z).norm.mul_const A)
  have hfixed := hu ((InnerProductSpace.toDual ℝ H) z)
  simp only [InnerProductSpace.toDual_apply_apply] at hfixed
  have hh := hzero.add hfixed
  simpa only [inner_sub_left, sub_add_cancel, zero_add] using hh

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- The planar current pairing of two L2 fields is integrable. Source: Morgan-Tian Lemma
19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem planarCircleCurrent_integrable (u v : Lp E 2 mu) :
    Integrable (fun x => planarCircleCurrent (u x) (v x)) mu := by
  have h : Integrable (fun x => inner ℝ ((quarterTurn.compLp u) x) (v x)) mu :=
    L2.integrable_inner (quarterTurn.compLp u) v
  apply h.congr
  filter_upwards [quarterTurn.coeFn_compLp u] with x hx
  rw [hx, quarterTurn_inner]

/-- The actual oriented current survives a strong-value/weak-column limit. No pointwise
derivative convergence or phase lift is assumed. Source: Morgan-Tian Lemma 19.15, pp.
447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem planarCircleCurrent_integral_tendsto
    {u v : ℕ → Lp E 2 mu} {U V : Lp E 2 mu}
    (hu : Tendsto u atTop (𝓝 U)) (hv : WeakConverges v V)
    {C : ℝ} (hC : ∀ j, ‖v j‖ ≤ C) :
    Tendsto (fun j => ∫ x, planarCircleCurrent (u j x) (v j x) ∂mu) atTop
      (𝓝 (∫ x, planarCircleCurrent (U x) (V x) ∂mu)) := by
  let T : Lp E 2 mu →L[ℝ] Lp E 2 mu := quarterTurn.compLpL 2 mu
  have hT : Tendsto (fun j => T (u j)) atTop (𝓝 (T U)) :=
    (T.continuous.tendsto U).comp hu
  have h := inner_tendsto_weak_strong hv hT hC
  have hid (a b : Lp E 2 mu) : inner ℝ (T a) b =
      ∫ x, planarCircleCurrent (a x) (b x) ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [quarterTurn.coeFn_compLp a] with x hx
    change inner ℝ ((quarterTurn.compLp a) x) (b x) = _
    rw [hx, quarterTurn_inner]
  simpa only [hid] using h

/-- A fixed linear reader of the compact target observations preserves the same genuine
current in the extracted sequence. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64
derivation `2026-09-25-free-label-compactness.md`. -/
theorem planarProjection_current_integral_tendsto
    {m : ℕ} (R : EuclideanSpace ℝ (Fin m) →L[ℝ] E)
    {u v : ℕ → Lp (EuclideanSpace ℝ (Fin m)) 2 mu}
    {U V : Lp (EuclideanSpace ℝ (Fin m)) 2 mu}
    (hu : Tendsto u atTop (𝓝 U)) (hv : WeakConverges v V)
    {C : ℝ} (hC : ∀ j, ‖v j‖ ≤ C) :
    Tendsto (fun j => ∫ x, planarCircleCurrent (R (u j x)) (R (v j x)) ∂mu) atTop
      (𝓝 (∫ x, planarCircleCurrent (R (U x)) (R (V x)) ∂mu)) := by
  let T := R.compLpL 2 mu
  have hU : Tendsto (fun j => T (u j)) atTop (𝓝 (T U)) :=
    (T.continuous.tendsto U).comp hu
  have hV : WeakConverges (fun j => T (v j)) (T V) := fun L => hv (L.comp T)
  have hb (j : ℕ) : ‖T (v j)‖ ≤ ‖R‖ * C :=
    (R.norm_compLp_le (v j)).trans (mul_le_mul_of_nonneg_left (hC j) (norm_nonneg _))
  have h := planarCircleCurrent_integral_tendsto hU hV hb
  have hid (a b : Lp (EuclideanSpace ℝ (Fin m)) 2 mu) :
      (∫ x, planarCircleCurrent (T a x) (T b x) ∂mu) =
        ∫ x, planarCircleCurrent (R (a x)) (R (b x)) ∂mu := by
    apply integral_congr_ae
    filter_upwards [R.coeFn_compLp a, R.coeFn_compLp b] with x hx hy
    change planarCircleCurrent ((R.compLp a) x) ((R.compLp b) x) = _
    rw [hx, hy]
  simpa only [hid] using h

end PoincareMT.M64
