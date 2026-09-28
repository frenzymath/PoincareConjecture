import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1VectorDecoder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps









set_option autoImplicit false

open AddCircle MeasureTheory Set
open scoped BigOperators

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]





theorem exists_periodicH1_core_composition {ι : Type*} [Fintype ι]
    (Φ : (ι → ℂ) → ℂ) (Φ1 : (ι → ℂ) → (ι → ℂ) →L[ℝ] ℂ)
    (hΦ : ∀ z, HasFDerivAt Φ (Φ1 z) z) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z, ‖Φ1 z‖ ≤ A)
    (hLip : ∀ z w, ‖Φ1 z - Φ1 w‖ ≤ B * ‖z - w‖) :
    ∃ f : {u : ι → lp (fun _ : ℤ => ℂ) 2 // ∀ i, u i ∈ periodicC1Core (L := L)} →
        lp (fun _ : ℤ => ℂ) 2,
      (∀ u x, periodicSobolevJet (L := L) 0 0 (by omega) (f u) x =
        Φ (periodicH1VectorDecoder (L := L) ι u x)) ∧
      ∀ u v, ‖f u - f v‖ ≤ 4 * (1 + (Fintype.card ι : ℝ)) *
        (A * ‖u.val - v.val‖ + B *
          ‖periodicH1VectorDecoder (L := L) ι (u.val - v.val)‖ * ‖v.val‖) := by
  classical
  let H := lp (fun _ : ℤ => ℂ) 2
  let X := ι → H
  let s : Set X := {u | ∀ i, u i ∈ periodicC1Core (L := L)}
  let D := periodicSobolevJet (L := L) 0 0 (by omega)
  let DX := periodicH1VectorDecoder (L := L) ι
  let N : ℝ := Fintype.card ι
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hi (q : C(AddCircle L, ℂ)) :
      Integrable (fun x => ‖q x‖ ^ 2) haarAddCircle :=
    (q.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiV (q : C(AddCircle L, ι → ℂ)) :
      Integrable (fun x => ‖q x‖ ^ 2) haarAddCircle :=
    (q.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnon (q : C(AddCircle L, ℂ)) :
      0 ≤ ∫ x : AddCircle L, ‖q x‖ ^ 2 ∂haarAddCircle :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hpi (z : ι → ℂ) : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
    have hsum : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    apply (Real.le_sqrt (norm_nonneg _) hsum).mp
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i))
  have henergy (u : X) (v : C(AddCircle L, ι → ℂ))
      (hv : ∀ i (x : ℝ), HasDerivAt (fun y : ℝ => D (u i) (y : AddCircle L))
        (v (x : AddCircle L) i) x) :
      (∫ x : AddCircle L, ‖DX u x‖ ^ 2 ∂haarAddCircle) ≤ N * ‖u‖ ^ 2 ∧
      (∫ x : AddCircle L, ‖v x‖ ^ 2 ∂haarAddCircle) ≤ N * ‖u‖ ^ 2 := by
    have hsum (q : C(AddCircle L, ι → ℂ))
        (hq : ∀ i, (∫ x : AddCircle L, ‖q x i‖ ^ 2 ∂haarAddCircle) ≤ ‖u i‖ ^ 2) :
        (∫ x : AddCircle L, ‖q x‖ ^ 2 ∂haarAddCircle) ≤ N * ‖u‖ ^ 2 := by
      have hqi (i : ι) : Integrable (fun x : AddCircle L => ‖q x i‖ ^ 2) haarAddCircle :=
        (((continuous_apply i).comp q.continuous).norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc
        _ ≤ ∫ x : AddCircle L, ∑ i, ‖q x i‖ ^ 2 ∂haarAddCircle :=
          integral_mono (hiV q) (integrable_finsetSum _ (fun i _ => hqi i)) (fun x => hpi (q x))
        _ = ∑ i, ∫ x : AddCircle L, ‖q x i‖ ^ 2 ∂haarAddCircle :=
          integral_finsetSum _ (fun i _ => hqi i)
        _ ≤ ∑ i, ‖u i‖ ^ 2 := Finset.sum_le_sum (fun i _ => hq i)
        _ ≤ ∑ _ : ι, ‖u‖ ^ 2 := Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2)
        _ = N * ‖u‖ ^ 2 := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
    have he (i : ι) : ‖u i‖ ^ 2 =
        (∫ x : AddCircle L, ‖D (u i) x‖ ^ 2 ∂haarAddCircle) +
          ∫ x : AddCircle L, ‖v x i‖ ^ 2 ∂haarAddCircle :=
      periodicH1Decoder_norm_sq (L := L) (u i)
        ⟨fun x => v x i, (continuous_apply i).comp v.continuous⟩ (hv i)
    constructor
    · apply hsum (DX u)
      intro i
      change (∫ x : AddCircle L, ‖D (u i) x‖ ^ 2 ∂haarAddCircle) ≤ ‖u i‖ ^ 2
      have hn : 0 ≤ ∫ x : AddCircle L, ‖v x i‖ ^ 2 ∂haarAddCircle :=
        integral_nonneg (fun _ => sq_nonneg _)
      linarith [he i]
    · apply hsum v
      intro i
      have hn := hnon (D (u i))
      linarith [he i]
  have hΦcont : Continuous Φ := continuous_iff_continuousAt.mpr (fun z => (hΦ z).continuousAt)
  have hΦ1cont : Continuous Φ1 :=
    (lipschitzWith_iff_norm_sub_le.mpr hLip : LipschitzWith ⟨B, hB⟩ Φ1).continuous
  have hΦlip (z w : ι → ℂ) : ‖Φ z - Φ w‖ ≤ A * ‖z - w‖ :=
    (convex_univ : Convex ℝ (univ : Set (ι → ℂ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (hΦ x).hasFDerivWithinAt) (fun x _ => hbound x) (mem_univ w) (mem_univ z)
  let g (u : s) (i : ι) : C(AddCircle L, ℂ) := (u.property i).choose
  have hg (u : s) (i : ι) (x : ℝ) :
      HasDerivAt (fun y : ℝ => D (u.val i) (y : AddCircle L)) (g u i (x : AddCircle L)) x :=
    (u.property i).choose_spec x
  let G (u : s) : C(AddCircle L, ι → ℂ) :=
    ⟨fun x i => g u i x, continuous_pi (fun i => (g u i).continuous)⟩
  let C (u : s) : C(AddCircle L, ℂ) :=
    ⟨fun x => Φ (DX u x), hΦcont.comp (DX u).continuous⟩
  let C1 (u : s) : C(AddCircle L, ℂ) :=
    ⟨fun x => Φ1 (DX u x) (G u x),
      (hΦ1cont.comp (DX u).continuous).clm_apply (G u).continuous⟩
  have hC (u : s) (x : ℝ) : HasDerivAt (fun y : ℝ => C u (y : AddCircle L))
      (C1 u (x : AddCircle L)) x := by
    have hvec : HasDerivAt (fun y : ℝ => DX u (y : AddCircle L))
        (G u (x : AddCircle L)) x := hasDerivAt_pi.mpr (fun i => hg u i x)
    exact (hΦ (DX u (x : AddCircle L))).comp_hasDerivAt x hvec
  let f (u : s) := periodicH1Coordinates (C u) (C1 u) (hC u)
  have hdecode (u : s) : D (f u) = C u := periodicH1Coordinates_reconstruct _ _ (hC u)
  refine ⟨f, fun u x => congrArg (fun q : C(AddCircle L, ℂ) => q x) (hdecode u), ?_⟩
  intro u v
  let P := ‖u.val - v.val‖
  let U := ‖DX (u.val - v.val)‖
  let Q := ‖v.val‖
  have hP : 0 ≤ P := norm_nonneg _
  have hU : 0 ≤ U := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  have hdelta := henergy (u.val - v.val) (G u - G v) (fun i x => by
    change HasDerivAt (fun y : ℝ => D ((u.val - v.val) i) (y : AddCircle L))
      (g u i (x : AddCircle L) - g v i (x : AddCircle L)) x
    simpa only [Pi.sub_apply, map_sub, ContinuousMap.sub_apply] using
      (hg u i x).fun_sub (hg v i x))
  have hv := henergy v.val (G v) (hg v)
  have hfun : (∫ x : AddCircle L, ‖(C u - C v) x‖ ^ 2 ∂haarAddCircle) ≤
      A ^ 2 * (N * P ^ 2) := by
    calc
      _ ≤ ∫ x : AddCircle L, A ^ 2 * ‖DX (u.val - v.val) x‖ ^ 2 ∂haarAddCircle := by
        apply integral_mono (hi (C u - C v)) ((hiV (DX (u.val - v.val))).const_mul _)
        intro x
        change ‖Φ (DX u x) - Φ (DX v x)‖ ^ 2 ≤ A ^ 2 * ‖DX (u.val - v.val) x‖ ^ 2
        simpa only [map_sub, ContinuousMap.sub_apply, mul_pow] using
          pow_le_pow_left₀ (norm_nonneg _) (hΦlip (DX u x) (DX v x)) 2
      _ = A ^ 2 * ∫ x : AddCircle L, ‖DX (u.val - v.val) x‖ ^ 2 ∂haarAddCircle :=
        integral_const_mul _ _
      _ ≤ A ^ 2 * (N * P ^ 2) := mul_le_mul_of_nonneg_left hdelta.1 (sq_nonneg _)
  have hder (x : AddCircle L) : ‖(C1 u - C1 v) x‖ ≤
      A * ‖(G u - G v) x‖ + (B * U) * ‖G v x‖ := by
    have hx : ‖DX u x - DX v x‖ ≤ U := by
      simpa only [U, map_sub, ContinuousMap.sub_apply] using (DX (u.val - v.val)).norm_coe_le_norm x
    have hsplit : (C1 u - C1 v) x =
        Φ1 (DX u x) ((G u - G v) x) + (Φ1 (DX u x) - Φ1 (DX v x)) (G v x) := by
      change Φ1 (DX u x) (G u x) - Φ1 (DX v x) (G v x) = _
      simp only [ContinuousMap.sub_apply, map_sub, sub_apply]
      abel
    rw [hsplit]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (Φ1 (DX u x)).le_of_opNorm_le (hbound _) _
    · exact (Φ1 (DX u x) - Φ1 (DX v x)).le_of_opNorm_le
        ((hLip _ _).trans (mul_le_mul_of_nonneg_left hx hB)) _
  have hderint : (∫ x : AddCircle L, ‖(C1 u - C1 v) x‖ ^ 2 ∂haarAddCircle) ≤
      2 * A ^ 2 * (N * P ^ 2) + 2 * (B * U) ^ 2 * (N * Q ^ 2) := by
    calc
      _ ≤ ∫ x : AddCircle L, 2 * A ^ 2 * ‖(G u - G v) x‖ ^ 2 +
          2 * (B * U) ^ 2 * ‖G v x‖ ^ 2 ∂haarAddCircle := by
        apply integral_mono (hi (C1 u - C1 v))
          (((hiV (G u - G v)).const_mul _).add ((hiV (G v)).const_mul _))
        intro x
        change ‖(C1 u - C1 v) x‖ ^ 2 ≤
          2 * A ^ 2 * ‖(G u - G v) x‖ ^ 2 + 2 * (B * U) ^ 2 * ‖G v x‖ ^ 2
        have ht := pow_le_pow_left₀ (norm_nonneg _) (hder x) 2
        nlinarith [sq_nonneg (A * ‖(G u - G v) x‖ - (B * U) * ‖G v x‖)]
      _ = 2 * A ^ 2 * (∫ x : AddCircle L, ‖(G u - G v) x‖ ^ 2 ∂haarAddCircle) +
          2 * (B * U) ^ 2 * ∫ x : AddCircle L, ‖G v x‖ ^ 2 ∂haarAddCircle := by
        rw [integral_add ((hiV (G u - G v)).const_mul _) ((hiV (G v)).const_mul _),
          integral_const_mul, integral_const_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left hdelta.2 (by positivity))
        (mul_le_mul_of_nonneg_left hv.2 (by positivity))
  have hCd (x : ℝ) : HasDerivAt (fun y : ℝ => (C u - C v) (y : AddCircle L))
      ((C1 u - C1 v) (x : AddCircle L)) x := by
    simpa only [ContinuousMap.sub_apply] using (hC u x).fun_sub (hC v x)
  have henc : periodicH1Coordinates (C u - C v) (C1 u - C1 v) hCd = f u - f v := by
    apply periodicH1Decoder_injective (L := L)
    rw [periodicH1Coordinates_reconstruct, map_sub, hdecode, hdecode]
  have he : ‖f u - f v‖ ^ 2 =
      (∫ x : AddCircle L, ‖(C u - C v) x‖ ^ 2 ∂haarAddCircle) +
        ∫ x : AddCircle L, ‖(C1 u - C1 v) x‖ ^ 2 ∂haarAddCircle := by
    rw [← henc]
    exact periodicH1Coordinates_norm_sq _ _ hCd
  have hs : ‖f u - f v‖ ^ 2 ≤ N * (3 * (A * P) ^ 2 + 2 * (B * U * Q) ^ 2) := by
    rw [he]
    exact (add_le_add hfun hderint).trans_eq (by ring)
  have ha : 0 ≤ A * P := mul_nonneg hA hP
  have hb : 0 ≤ B * U * Q := mul_nonneg (mul_nonneg hB hU) hQ
  have hnum : 3 * (A * P) ^ 2 + 2 * (B * U * Q) ^ 2 ≤
      (4 * (A * P + B * U * Q)) ^ 2 := by
    nlinarith [mul_nonneg ha hb]
  have hNs : N ≤ (1 + N) ^ 2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * (1 + N) *
    (A * P + B * U * Q))).mp
  calc
    _ ≤ N * (3 * (A * P) ^ 2 + 2 * (B * U * Q) ^ 2) := hs
    _ ≤ (1 + N) ^ 2 * (3 * (A * P) ^ 2 + 2 * (B * U * Q) ^ 2) :=
      mul_le_mul_of_nonneg_right hNs (by positivity)
    _ ≤ (1 + N) ^ 2 * (4 * (A * P + B * U * Q)) ^ 2 :=
      mul_le_mul_of_nonneg_left hnum (sq_nonneg _)
    _ = _ := by ring

end PoincareConjecture.M63
