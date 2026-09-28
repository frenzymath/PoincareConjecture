import PoincareConjecture.Proofs.M62.Lemma19_6_Orthogonality
import PoincareConjecture.Proofs.M62.Lemma19_6_InteriorRegularity
import PoincareConjecture.Proofs.M62.Sec19_1_MetricVariation
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion
import PoincareConjecture.Proofs.M04.RicciRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem hasDerivAt_speed_sq (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    HasDerivAt (fun s ↦ (curveSpeed F c s x) ^ 2)
      (-2 * (m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
        (curveSpeed F c t x) ^ 2) t := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) := ⟨Set.mem_univ _, ht⟩
  have htime : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun s : ℝ ↦ (x, s)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hspace : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun y : ℝ ↦ (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hγtime := (((hc.joint_smooth (x, t) hmem).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp t htime
  have hXtime := ((((spatial_velocity_joint_contMDiff F c hc) (x, t) hmem).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp t htime
  have hHspace := ((((curvature_joint_contMDiff F c hc) (x, t) hmem).contMDiffAt
    (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp x hspace
  have hS := (unitTangent_contMDiff F c hc hclosed x).mdifferentiableAt (by simp)
  have hγspace := (hc.spatial_regular t hclosed x).mdifferentiableAt (by norm_num)
  let D := F.connection t
  let X := fun y ↦ curveVelocity (n := n) (fun z ↦ c z t) y
  let S := spatialUnitTangent F c t
  let H := m62CurvatureVector F c t
  let v := curveSpeed F c t x
  have hv : v ≠ 0 := (speed_pos F c hc hclosed x).ne'
  have hX : X x = v • S x := by
    symm
    change v • (v⁻¹ • X x) = X x
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDS : rampHorizontalCovariantDerivative D (fun y ↦ c y t) S x = v • H x := by
    symm
    change v • (v⁻¹ • rampHorizontalCovariantDerivative D (fun y ↦ c y t) S x) = _
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hpair : HasDerivAt (fun y ↦ (F.metric t).inner (c y t) (S y) (H y))
      ((F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative D (fun y ↦ c y t) S x) (H x) +
      (F.metric t).inner (c x t) (S x)
        (rampHorizontalCovariantDerivative D (fun y ↦ c y t) H x)) x :=
    hasDerivAt_metric_pairing D hγspace hS hHspace
  have hzero : (fun y ↦ (F.metric t).inner (c y t) (S y) (H y)) = fun _ : ℝ ↦ 0 := by
    funext y
    rw [(F.metric t).symm (c y t) (S y) (H y)]
    exact curvature_unitTangent_inner_zero F c hc hclosed y
  rw [hzero] at hpair
  have hvalue := hpair.unique (hasDerivAt_const x (0 : ℝ))
  rw [hDS] at hvalue
  simp only [map_smul, smul_apply, smul_eq_mul] at hvalue
  have hcrossS : (F.metric t).inner (c x t) (S x)
      (rampHorizontalCovariantDerivative D (fun y ↦ c y t) H x) =
        -v * m62CurvatureSquared F c t x := by
    change v * m62CurvatureSquared F c t x + _ = 0 at hvalue
    linarith
  have hcross : (F.metric t).inner (c x t) (X x)
      (rampHorizontalCovariantDerivative D (fun y ↦ c y t) H x) =
        -v ^ 2 * m62CurvatureSquared F c t x := by
    rw [hX]
    simp only [map_smul, smul_apply, smul_eq_mul, hcrossS]
    ring
  have hcross' := (F.metric t).symm (c x t)
    (rampHorizontalCovariantDerivative D (fun y ↦ c y t) H x) (X x)
  rw [hcross] at hcross'
  obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_ricciEvaluation D).1 (c x t)
  have hscale := A.map_smul_univ (fun _ : Fin 2 ↦ v) (fun _ : Fin 2 ↦ S x)
  rw [← hA, ← hA] at hscale
  have hRic : D.ricci (c x t) (X x) (X x) = v ^ 2 * m62TangentRicci F c t x := by
    rw [hX]
    simpa only [LeviCivitaData.ricciEvaluation, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, m62TangentRicci, D, S] using hscale
  have hcommute := pullback_velocity_commute D c hopen hc.joint_smooth hmem
  have heq : (fun y ↦ curveVelocity (fun s ↦ c y s) t) = H :=
    funext (hc.equation t ht)
  rw [heq] at hcommute
  have hflow := hasDerivAt_flow_metric_pairing F (γ := fun s ↦ c x s)
    (Y := fun s ↦ curveVelocity (fun y ↦ c y s) x)
    (Z := fun s ↦ curveVelocity (fun y ↦ c y s) x) ht hγtime hXtime hXtime
  apply (hflow.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s ↦ speed_sq F c s x))).congr_deriv
  rw [hcommute]
  change -2 * D.ricci (c x t) (X x) (X x) +
    (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun y ↦ c y t) H x) (X x) +
    (F.metric t).inner (c x t) (X x)
      (rampHorizontalCovariantDerivative D (fun y ↦ c y t) H x) = _
  rw [hcross, hcross', hRic]
  ring

theorem hasDerivAt_speed (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    HasDerivAt (fun s ↦ curveSpeed F c s x)
      (-(m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
        curveSpeed F c t x) t := by
  have hv := (speed_pos F c hc (Set.Ioo_subset_Icc_self ht) x).ne'
  have h := (hasDerivAt_speed_sq F c hc ht x).sqrt (pow_ne_zero 2 hv)
  have heq : (fun s ↦ curveSpeed F c s x) =ᶠ[𝓝 t]
      (fun s ↦ Real.sqrt (curveSpeed F c s x ^ 2)) :=
    Filter.Eventually.of_forall fun s ↦ (Real.sqrt_sq (speed_nonneg F c s x)).symm
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  rw [Real.sqrt_sq (speed_nonneg F c t x)]
  field_simp

end PoincareConjecture.M62
