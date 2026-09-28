import PoincareConjecture.Proofs.M35.CapGeometry.RadialCylinderTensor
import PoincareConjecture.Proofs.M35.CapGeometry.VanishingMetricErrorJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => RoundCylinderCoordinates

theorem radialCylinderTensor_jetError_tendsto_zero
    (A : ℕ → ℝ → ℝ) (b s : ℕ → ℝ) (s₀ : ℝ) (q : ℕ → UnitTwoSphere)
    (order : ℕ) (hs : Tendsto s atTop (𝓝 s₀)) (hb : Tendsto b atTop (𝓝 1))
    (hA : ∀ k, ContDiffAt ℝ ∞ (A k) (s k))
    (hjet : ∀ r ≤ order, Tendsto
      (fun k => iteratedFDeriv ℝ r (fun y => A k y - 2) (s k)) atTop (𝓝 0)) :
    Tendsto (fun k => roundCylinderJetErrorSquared 0 (radialCylinderTensor (A k) (b k))
      order (q k, s k)) atTop (𝓝 0) := by
  let p (k : ℕ) : V := (0, s k)
  let p₀ : V := (0, s₀)
  have hp : Tendsto p atTop (𝓝 p₀) := tendsto_const_nhds.prodMk_nhds hs
  have hfixed (h : V → ℝ) (hh : ContDiff ℝ ∞ h) (r : ℕ) :
      HasUniformJetBoundsAt r (fun _ : ℕ => h) p := by
    intro j _hj
    have hc := (hh.contDiffAt.continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top (a := (j : ℕ∞)))).tendsto.comp hp
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hc).exists_norm_le
    exact ⟨C, fun k => hC _ (mem_range_self k)⟩
  let angular (i j : Fin 3) (y : V) :=
    (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q 0)) y i j -
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2) / 2
  have hang (i j : Fin 3) : ContDiff ℝ ∞ (angular i j) :=
    ((contDiff_roundCylinderGram 0 (q 0) i j).sub contDiff_const).div_const 2
  let F k (y : V) := A k y.2 - 2
  have hF (k : ℕ) : ContDiffAt ℝ ∞ (F k) (p k) :=
    ((hA k).comp (p k) contDiffAt_snd).sub contDiffAt_const
  have hFjet (r : ℕ) (hr : r ≤ order) : Tendsto
      (fun k => iteratedFDeriv ℝ r (F k) (p k)) atTop (𝓝 0) := by
    change Tendsto (fun k => iteratedFDeriv ℝ r
      ((fun y => A k y - 2) ∘ (Prod.snd : V → ℝ)) (p k)) atTop (𝓝 0)
    apply jet_comp_tendsto_zero_of_bounded (hfixed (Prod.snd : V → ℝ) contDiff_snd r)
      (Eventually.of_forall fun _ => contDiffAt_snd)
      (Eventually.of_forall fun k => (hA k).sub contDiffAt_const)
    exact fun j hj => hjet j (hj.trans hr)
  have hbzero : Tendsto (fun k => b k ^ 2 - 1) atTop (𝓝 0) := by
    simpa only [one_pow, sub_self] using (hb.pow 2).sub_const 1
  have hcjet (r : ℕ) : Tendsto
      (fun k => iteratedFDeriv ℝ r (fun _ : V => b k ^ 2 - 1) (p k)) atTop (𝓝 0) := by
    cases r with
    | zero =>
      have h := ((continuousMultilinearCurryFin0 ℝ V ℝ).symm.continuous.tendsto 0).comp
        hbzero
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, map_zero] using h
    | succ r =>
      simpa only [iteratedFDeriv_succ_const, Pi.zero_apply] using tendsto_const_nhds
  have herr (r : ℕ) (hr : r ≤ order) (i j : Fin 3) : Tendsto
      (fun k => iteratedFDeriv ℝ r (fun y =>
        roundCylinderTensorCoefficient (radialCylinderTensor (A k) (b k))
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j) (p k))
      atTop (𝓝 0) := by
    let c := (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2
    have h1 := jet_bilinear_tendsto_zero_of_bounded (ContinuousLinearMap.mul ℝ ℝ)
      (fun l hl => hFjet l (hl.trans hr)) (hfixed (angular i j) (hang i j) r)
      (Eventually.of_forall hF) (Eventually.of_forall fun _ => (hang i j).contDiffAt)
    have h2 := jet_bilinear_tendsto_zero_of_bounded (ContinuousLinearMap.mul ℝ ℝ)
      (fun l _ => hcjet l) (hfixed (fun _ : V => c) contDiff_const r)
      (Eventually.of_forall fun _ => contDiffAt_const)
      (Eventually.of_forall fun _ => contDiffAt_const)
    have hsum := h1.add h2
    simp only [add_zero] at hsum
    apply hsum.congr'
    filter_upwards [] with k
    have heq : (fun y : V =>
        roundCylinderTensorCoefficient (radialCylinderTensor (A k) (b k))
          (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y i j) =
      (fun y => F k y * angular i j y + (b k ^ 2 - 1) * c) := by
      funext y
      have h := radialCylinderTensor_coefficient_error (A k) (b k) (q k) (q 0) y i j
      simpa only [F, angular, c, mul_assoc] using h
    rw [heq]
    have horder : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    exact (fun_iteratedFDeriv_add_apply
      (((hF k).mul (hang i j).contDiffAt).of_le horder)
      ((contDiffAt_const (c := (b k ^ 2 - 1) * c)).of_le horder)).symm
  have h := roundCylinderJetDifferenceSquared_tendsto_zero order
    (fun _ => 0) (fun _ => zero_lt_one) 0 zero_lt_one tendsto_const_nhds q
    (fun k => radialCylinderTensor (A k) (b k)) (fun _ => RoundCylinderMetric)
    s s₀ hs (fun k i j => radialCylinderTensor_coefficient_contDiffAt (b k) (q k) (hA k) i j)
    (fun k i j => (contDiff_roundCylinderGram 0 (q k) i j).contDiffAt) herr
  simpa only [RoundCylinderMetric, roundCylinderJetDifferenceSquared_model] using h

end PoincareConjecture.M35
