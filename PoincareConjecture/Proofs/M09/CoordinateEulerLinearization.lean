import PoincareConjecture.Proofs.M09.CoordinatePhase
import PoincareConjecture.Proofs.M09.CoordinateCompatibility
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.LinearCombination








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem regularizedCoordinatePhase_connection_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ)
    (s : ℝ) (y a W : E) (hpos : ∀ v : E, v ≠ 0 → 0 < G (s, y) v v) :
    G (s, y) ((regularizedCoordinatePhase G R (s, (y, a))).2 +
      coordinateConnectionBilinear G (s, y) a a) W -
      2 * s ^ 2 * fderiv ℝ R (s, y) (0, W) + fderiv ℝ G (s, y) (1, 0) a W = 0 := by
  rw [map_add, add_apply, regularizedCoordinatePhase_pairing G R (s, y) hpos,
    coordinateConnectionBilinear_apply, coordinateConnection_pairing G (s, y) hpos]
  ring

theorem regularizedCoordinatePhase_linearized_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (s : ℝ) (y : E) (hz : (s, y) ∈ U) (a v w W : E) :
    let C := coordinateConnectionBilinear G
    let B := regularizedCoordinatePhase G R
    let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ fderiv ℝ G (s, x) (1, 0)
    let P : E → E →L[ℝ] ℝ := fun x ↦
      (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    let alpha := (B (s, (y, a))).2
    let beta := (fderiv ℝ B (s, (y, a)) (0, (v, w))).2
    fderiv ℝ G (s, y) (0, v) (alpha + C (s, y) a a) W +
      G (s, y) (beta + fderiv ℝ C (s, y) (0, v) a a + C (s, y) w a + C (s, y) a w) W -
      2 * s ^ 2 * fderiv ℝ P y v W + fderiv ℝ H y v a W + H y w W = 0 := by
  let C := coordinateConnectionBilinear G
  let B := regularizedCoordinatePhase G R
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ fderiv ℝ G (s, x) (1, 0)
  let P : E → E →L[ℝ] ℝ := fun x ↦
    (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
  let x : ℝ → E := fun u ↦ y + u • v
  let A : ℝ → E := fun u ↦ a + u • w
  have hx : HasDerivAt x v 0 := by
    simpa only [x, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have ha : HasDerivAt A w 0 := by
    simpa only [A, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
  have hx0 : x 0 = y := by simp [x]
  have ha0 : A 0 = a := by simp [A]
  have hmap : HasDerivAt (fun u ↦ (s, x u)) ((0, v) : ℝ × E) 0 :=
    (hasDerivAt_const 0 s).prodMk hx
  have hGa := hG.contDiffAt (hU.mem_nhds hz)
  have hCa : ContDiffAt ℝ ∞ C (s, y) :=
    (coordinateConnectionBilinear_contDiffOn G U hU hG hpos).contDiffAt (hU.mem_nhds hz)
  have hGline := (hGa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hmap
    (by rw [hx0])
  have hCline := (hCa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hmap
    (by rw [hx0])
  have hB : ContDiffAt ℝ ∞ B (s, (y, a)) :=
    (regularizedCoordinatePhase_smooth G R U hU hG hR hpos).contDiffAt
      ((hU.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mem_nhds hz)
  have hBline0 : HasDerivAt (fun u : ℝ ↦ B (s, (x u, A u)))
      ((fderiv ℝ B (s, (y, a))) (0, (v, w))) 0 := by
    simpa only [Function.comp_def] using
      (hB.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
        ((hasDerivAt_const 0 s).prodMk (hx.prodMk ha)) (by rw [hx0, ha0])
  have hBline : HasDerivAt (fun u : ℝ ↦ (B (s, (x u, A u))).2)
      (((fderiv ℝ B (s, (y, a))) (0, (v, w))).2) 0 := by
    convert (hBline0.hasFDerivAt.snd).hasDerivAt using 1 <;>
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  have hCaa := (hCline.clm_apply ha).clm_apply ha
  have hleft := (hGline.clm_apply (hBline.add hCaa)).clm_apply (hasDerivAt_const 0 W)
  have hslice : ContDiffAt ℝ ∞ (fun x : E ↦ (s, x)) y := contDiffAt_const.prodMk contDiffAt_id
  have hHa : ContDiffAt ℝ ∞ H y :=
    ((hGa.fderiv_right (m := ∞) (by simp)).comp y hslice).clm_apply contDiffAt_const
  have hPa : ContDiffAt ℝ ∞ P y :=
    ((((hR.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := ∞) (by simp)).comp y hslice)).clm_comp
      contDiffAt_const
  have hHline := (hHa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hx hx0.symm
  have hPline := (hPa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hx hx0.symm
  have hforce := (hPline.clm_apply (hasDerivAt_const 0 W)).const_mul (2 * s ^ 2)
  have htime := (hHline.clm_apply ha).clm_apply (hasDerivAt_const 0 W)
  have htotal := (hleft.sub hforce).add htime
  have heq : (fun u ↦ G (s, x u) ((B (s, (x u, A u))).2 + C (s, x u) (A u) (A u)) W -
      2 * s ^ 2 * P (x u) W + H (x u) (A u) W) =ᶠ[𝓝 (0 : ℝ)] (fun _ ↦ 0) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds
      (show U ∈ 𝓝 (s, x 0) by rw [hx0]; exact hU.mem_nhds hz)] with u hu
    exact regularizedCoordinatePhase_connection_pairing G R s (x u) (A u) W (hpos _ hu)
  have hzero := (htotal.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 (0 : ℝ))
  have hPzero : ((P ∘ x) 0) (0 : E) = 0 := by
    exact map_zero ((P ∘ x) 0)
  have hHzero : ((H ∘ x) 0) (A 0) (0 : E) = 0 := by
    exact map_zero (((H ∘ x) 0) (A 0))
  rw [hPzero, hHzero, add_zero] at hzero
  dsimp only at ⊢
  simpa [Function.comp_def, B, C, H, P, x, A, hx0, ha0, add_assoc] using hzero

theorem regularizedCoordinatePhase_covariant_linearized_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (hsym : ∀ z ∈ U, ∀ v w : E, G z v w = G z w v)
    (s : ℝ) (y : E) (hz : (s, y) ∈ U) (a v w W : E) :
    let C := coordinateConnectionBilinear G
    let B := regularizedCoordinatePhase G R
    let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ fderiv ℝ G (s, x) (1, 0)
    let P : E → E →L[ℝ] ℝ := fun x ↦
      (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    let alpha := (B (s, (y, a))).2
    let beta := (fderiv ℝ B (s, (y, a)) (0, (v, w))).2
    G (s, y) (beta + fderiv ℝ C (s, y) (0, v) a a +
        (2 : ℝ) • C (s, y) a w + C (s, y) v (alpha + C (s, y) a a)) W -
      2 * s ^ 2 * (fderiv ℝ P y v W - P y (C (s, y) v W)) +
      (fderiv ℝ H y v a W - H y (C (s, y) v a) W - H y a (C (s, y) v W)) +
      H y (w + C (s, y) a v) W = 0 := by
  let C := coordinateConnectionBilinear G
  let B := regularizedCoordinatePhase G R
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ fderiv ℝ G (s, x) (1, 0)
  let P : E → E →L[ℝ] ℝ := fun x ↦
    (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hGa := (hG.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hGs : ∀ᶠ z in 𝓝 (s, y), ∀ v w, G z v w = G z w v := by
    filter_upwards [hU.mem_nhds hz] with z hz'
    exact hsym z hz'
  have hCs (u v : E) : C (s, y) u v = C (s, y) v u :=
    coordinateConnection_symm G (s, y) hGa hGs u v
  have hlin := regularizedCoordinatePhase_linearized_pairing G R U hU hG hR hpos
    s y hz a v w W
  have hcompat := coordinateConnection_compatible G (s, y) hGa hGs (hpos _ hz)
    v ((B (s, (y, a))).2 + C (s, y) a a) W
  have heuler := regularizedCoordinatePhase_connection_pairing G R s y a
    (C (s, y) v W) (hpos _ hz)
  change G (s, y) ((B (s, (y, a))).2 + C (s, y) a a) (C (s, y) v W) -
    2 * s ^ 2 * P y (C (s, y) v W) + H y a (C (s, y) v W) = 0 at heuler
  change fderiv ℝ G (s, y) (0, v) ((B (s, (y, a))).2 + C (s, y) a a) W =
    G (s, y) (C (s, y) v ((B (s, (y, a))).2 + C (s, y) a a)) W +
      G (s, y) ((B (s, (y, a))).2 + C (s, y) a a) (C (s, y) v W) at hcompat
  change fderiv ℝ G (s, y) (0, v) ((B (s, (y, a))).2 + C (s, y) a a) W +
    G (s, y) ((fderiv ℝ B (s, (y, a)) (0, (v, w))).2 +
      fderiv ℝ C (s, y) (0, v) a a + C (s, y) w a + C (s, y) a w) W -
      2 * s ^ 2 * fderiv ℝ P y v W + fderiv ℝ H y v a W + H y w W = 0 at hlin
  rw [hcompat, hCs w a] at hlin
  change G (s, y) ((fderiv ℝ B (s, (y, a)) (0, (v, w))).2 +
      fderiv ℝ C (s, y) (0, v) a a + (2 : ℝ) • C (s, y) a w +
      C (s, y) v ((B (s, (y, a))).2 + C (s, y) a a)) W -
    2 * s ^ 2 * (fderiv ℝ P y v W - P y (C (s, y) v W)) +
    (fderiv ℝ H y v a W - H y (C (s, y) v a) W - H y a (C (s, y) v W)) +
    H y (w + C (s, y) a v) W = 0
  rw [hCs v a]
  simp only [two_smul, map_add, add_apply] at hlin heuler ⊢
  linear_combination hlin - heuler

end PoincareConjecture.Proofs.M09
