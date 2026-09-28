import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.CircleCurrentLimit
import Mathlib.MeasureTheory.Function.Holder








set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M64

local notation "E" => EuclideanSpace ℝ (Fin 2)

private def rotation : E →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (1 : Fin 2) 1)).comp
      (EuclideanSpace.proj 0) -
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 2) 1)).comp
      (EuclideanSpace.proj 1)



def planarCurrentBilinear : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp rotation



theorem planarCurrentBilinear_apply (u v : E) :
    planarCurrentBilinear u v = planarCircleCurrent u v := by
  simp [planarCurrentBilinear, rotation, planarCircleCurrent,
    EuclideanSpace.inner_single_left]

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}




theorem strongSquare_toLp_tendsto
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : ℕ → X → F) (u : X → F) (hf : ∀ j, MemLp (f j) 2 mu) (hu : MemLp u 2 mu)
    (hlim : Tendsto (fun j => ∫ x, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hu.toLp u)) := by
  have hn (j : ℕ) : ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2 =
      ∫ x, ‖f j x - u x‖ ^ 2 ∂mu := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf j).toLp (f j)) (hu.toLp u),
      (hf j).coeFn_toLp, hu.coeFn_toLp] with x hx hfx hux
    simp only [hx, Pi.sub_apply, hfx, hux]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun j => ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hn] using hlim
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt




theorem strongSquare_planarCurrent_pairing_tendsto
    (f g : ℕ → X → E) (u v : X → E)
    (hf : ∀ j, MemLp (f j) 2 mu) (hg : ∀ j, MemLp (g j) 2 mu)
    (hu : MemLp u 2 mu) (hv : MemLp v 2 mu)
    (hfu : Tendsto (fun j => ∫ x, ‖f j x - u x‖ ^ 2 ∂mu) atTop (𝓝 0))
    (hgv : Tendsto (fun j => ∫ x, ‖g j x - v x‖ ^ 2 ∂mu) atTop (𝓝 0))
    (phi : X → ℝ) (hp : MemLp phi ∞ mu) :
    Tendsto (fun j => ∫ x, phi x * planarCircleCurrent (f j x) (g j x) ∂mu) atTop
      (𝓝 (∫ x, phi x * planarCircleCurrent (u x) (v x) ∂mu)) := by
  let U := hu.toLp u
  let V := hv.toLp v
  let F := fun j => (hf j).toLp (f j)
  let G := fun j => (hg j).toLp (g j)
  let P := hp.toLp phi
  let T : Lp E 2 mu →L[ℝ] Lp E 2 mu :=
    (ContinuousLinearMap.lsmul ℝ ℝ).holderL mu ∞ 2 2 P
  let B := planarCurrentBilinear.lpPairing mu 2 2
  have hF : Tendsto F atTop (𝓝 U) := strongSquare_toLp_tendsto f u hf hu hfu
  have hG : Tendsto G atTop (𝓝 V) := strongSquare_toLp_tendsto g v hg hv hgv
  have hc : Continuous (fun q : Lp E 2 mu × Lp E 2 mu => B (T q.1) q.2) :=
    (B.continuous.comp (T.continuous.comp continuous_fst)).clm_apply continuous_snd
  have h := (hc.tendsto (U, V)).comp (hF.prodMk_nhds hG)
  change Tendsto (fun j => B (T (F j)) (G j)) atTop (𝓝 (B (T U) V)) at h
  have hid (a b : X → E) (ha : MemLp a 2 mu) (hb : MemLp b 2 mu) :
      B (T (ha.toLp a)) (hb.toLp b) =
        ∫ x, phi x * planarCircleCurrent (a x) (b x) ∂mu := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [((ContinuousLinearMap.lsmul ℝ ℝ) : ℝ →L[ℝ] E →L[ℝ] E).coeFn_holder
      (r := 2) P (ha.toLp a), hp.coeFn_toLp, ha.coeFn_toLp, hb.coeFn_toLp]
      with x hx hpx hax hbx
    change planarCurrentBilinear
      (((ContinuousLinearMap.lsmul ℝ ℝ).holder 2 P (ha.toLp a)) x) ((hb.toLp b) x) = _
    rw [hx, hpx, hax, hbx]
    simp only [ContinuousLinearMap.lsmul_apply, map_smul, smul_apply,
      smul_eq_mul, planarCurrentBilinear_apply]
  simpa only [F, G, U, V, hid] using h

end PoincareConjecture.M64
