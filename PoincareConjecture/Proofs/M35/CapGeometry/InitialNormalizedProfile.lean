import PoincareConjecture.Proofs.M35.CapGeometry.InitialProfileJets
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCylinderJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem initial_normalized_radial_jetError_tendsto_zero
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (t a s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta)
    {t₀ s₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (halim : Tendsto a atTop atTop) (hslim : Tendsto s atTop (𝓝 s₀))
    (q : ℕ → UnitTwoSphere) (order : ℕ) :
    let Q k := (E.flow.connection (t k)).scalarCurvature
      (rawInverseRadius P E.flow.base E.rotation_invariant (t k) (a k) •
        EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    let b k := (Real.sqrt (Q k))⁻¹
    Tendsto (fun k => roundCylinderJetErrorSquared 0 (radialCylinderTensor
      (fun u => Q k * rawWarpingRadius P E.flow.base E.rotation_invariant
        (t k) (a k + b k * u) ^ 2) 1) order (q k, s k)) atTop (𝓝 0) := by
  let Q k := (E.flow.connection (t k)).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant (t k) (a k) •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b k := (Real.sqrt (Q k))⁻¹
  let f k := rawWarpingRadius P E.flow.base E.rotation_invariant (t k)
  let A k u := Q k * f k (a k + b k * u) ^ 2
  let r k := a k + b k * s k
  have hQlim : Tendsto Q atTop (𝓝 (1 / (1 - t₀))) :=
    initial_intrinsic_axis_scalar_tendsto P E ⟨htheta.le, hthetalt⟩ t a ht
      ht₀ htlim halim
  have hb : Tendsto b atTop (𝓝 ((Real.sqrt (1 / (1 - t₀)))⁻¹)) :=
    ((Real.continuous_sqrt.tendsto _).comp hQlim).inv₀
      (Real.sqrt_pos.mpr (one_div_pos.mpr (sub_pos.mpr ht₀))).ne'
  have hrlim : Tendsto r atTop atTop := halim.atTop_add (hb.mul hslim)
  have hf (k : ℕ) : ContDiff ℝ ∞ (f k) := by
    have hk : t k ∈ Ico 0 E.flow.base.lifetime := ⟨(ht k).1, (ht k).2.trans_lt hthetalt⟩
    change ContDiff ℝ ∞ (rawWarpingRadius P E.flow.base E.rotation_invariant (t k))
    rw [rawWarpingRadius_eq P E.flow.base E.rotation_invariant hk]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hA (k : ℕ) : ContDiff ℝ ∞ (A k) :=
    contDiff_const.mul (((hf k).pow 2).comp
      (contDiff_const.add (contDiff_const.mul contDiff_id)))
  have hAjet (m : ℕ) : Tendsto (fun k => iteratedDeriv m (A k) (s k))
      atTop (𝓝 (if m = 0 then 2 else 0)) := by
    have hprofile := initial_intrinsic_squared_radius_jets_tendsto_of_escape P E
      htheta hthetalt t r ht ht₀ htlim hrlim m
    have hformula (k : ℕ) : iteratedDeriv m (A k) (s k) =
        Q k * b k ^ m * iteratedDeriv m (fun u => f k u ^ 2) (r k) := by
      change iteratedDeriv m (fun u => Q k * f k (a k + b k * u) ^ 2) (s k) = _
      rw [iteratedDeriv_const_mul_field]
      have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (m : ℕ∞))
      have hc : ContDiff ℝ m (fun u => f k (a k + u) ^ 2) :=
        (((hf k).pow 2).comp (contDiff_const.add contDiff_id)).of_le hm
      have hh := congrFun (iteratedDeriv_comp_const_mul hc (b k)) (s k)
      rw [iteratedDeriv_comp_const_add (f := fun u => f k u ^ 2) (s := a k) (n := m)] at hh
      rw [hh]
      exact mul_assoc _ _ _ |>.symm
    have hh := (hQlim.mul (hb.pow m)).mul hprofile
    have hvalue : (1 / (1 - t₀)) * ((Real.sqrt (1 / (1 - t₀)))⁻¹) ^ m *
        (if m = 0 then 2 * (1 - t₀) else 0) = (if m = 0 then 2 else 0) := by
      by_cases hm : m = 0
      · simp only [hm, pow_zero, mul_one, ite_true]
        field_simp [(sub_pos.mpr ht₀).ne']
      · simp only [if_neg hm, mul_zero]
    rw [hvalue] at hh
    simpa only [hformula, f] using hh
  apply radialCylinderTensor_jetError_tendsto_zero A (fun _ => 1) s s₀ q order
    hslim tendsto_const_nhds (fun k => (hA k).contDiffAt)
  intro m _hm
  have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (m : ℕ∞))
  have herr : Tendsto (fun k => iteratedDeriv m (fun u => A k u - 2) (s k))
      atTop (𝓝 0) := by
    have heq (k : ℕ) : iteratedDeriv m (fun u => A k u - 2) (s k) =
        iteratedDeriv m (A k) (s k) - (if m = 0 then 2 else 0) := by
      rw [iteratedDeriv_fun_sub ((hA k).contDiffAt.of_le hm) contDiffAt_const,
        iteratedDeriv_const]
    simp_rw [heq]
    simpa only [sub_self] using (hAjet m).sub_const (if m = 0 then 2 else 0)
  have hh := ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).continuous.tendsto 0).comp
    herr
  simpa only [iteratedFDeriv_eq_equiv_comp, Function.comp_def, map_zero] using hh

end PoincareConjecture.M35.Uniqueness
