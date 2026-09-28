import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1NormalVelocityCommutation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Definitions.M63Ramp
import PoincareConjecture.Proofs.M62.Lemma0_1_Speed
import PoincareConjecture.Proofs.M62.Sec19_1_MetricVariation
import PoincareConjecture.Proofs.M04.RicciRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_speed_hasDerivAt_of_curvature_c1
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J)
    (hH : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ interior J))
    {t : ℝ} (ht : t ∈ interior J) (x : ℝ) :
    HasDerivAt (fun s => curveSpeed F c s x)
      (-(m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
        curveSpeed F c t x) t := by
  have htJ : t ∈ J := interior_subset ht
  have htF : t ∈ Ioo a b := by
    simpa only [interior_Icc] using interior_mono hc.domain_subset ht
  have hopen : IsOpen (univ ×ˢ interior J : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_interior
  have hmem : (x, t) ∈ (univ ×ˢ interior J : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (x, s)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hspace (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun z : ℝ => (z, t)) y :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hgammaTime := ((hc.joint_c1.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
    (by norm_num)).comp t htime
  have hgammaSpace (y : ℝ) :=
    (hc.spatial_regular t htJ y).mdifferentiableAt (by norm_num)
  have hS (y : ℝ) :=
    (unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t htJ)
      (hc.immersed t htJ) y).mdifferentiableAt (by norm_num)
  have hHspace := ((hH.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
    (by norm_num)).comp x (hspace x)
  have hT : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, curveVelocity (fun s => c z.1 s) z.2⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ interior J) := by
    apply hH.congr
    intro z hz
    exact congrArg (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (c z.1 z.2))
      (hc.equation z.2 hz.2 z.1)
  let D := F.connection t
  obtain ⟨hXtime, hcommute⟩ :=
    pullback_velocity_commute_of_time_velocity_c1 D c hopen hc.joint_c1 hT hmem
  let X := fun y => curveVelocity (n := n) (fun z => c z t) y
  let S := spatialUnitTangent F c t
  let H := m62CurvatureVector F c t
  let v := curveSpeed F c t x
  have hspeed (y : ℝ) : 0 < curveSpeed F c t y :=
    Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t htJ y))
  have hv : v ≠ 0 := (hspeed x).ne'
  have hunit (y : ℝ) : (F.metric t).inner (c y t) (S y) (S y) = 1 := by
    have hne := (hspeed y).ne'
    simp only [S, spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
    rw [← M62.speed_sq F c t y]
    field_simp
  have horth (y : ℝ) : (F.metric t).inner (c y t) (H y) (S y) = 0 := by
    have hpair := M62.hasDerivAt_metric_pairing D (hgammaSpace y) (hS y) (hS y)
    have hconst : (fun z => (F.metric t).inner (c z t) (S z) (S z)) =
        fun _ : ℝ => (1 : ℝ) := funext hunit
    rw [hconst] at hpair
    have heq := hpair.unique (hasDerivAt_const y (1 : ℝ))
    have hz : (F.metric t).inner (c y t)
        (rampHorizontalCovariantDerivative D (fun z => c z t) S y) (S y) = 0 := by
      rw [(F.metric t).symm (c y t) (S y)] at heq
      linarith
    dsimp only [D, S] at hz
    simp only [H, S, m62CurvatureVector, m62SpatialDerivative, map_smul, smul_apply,
      smul_eq_mul, hz, mul_zero]
  have hX : X x = v • S x := by
    symm
    change v • (v⁻¹ • X x) = X x
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDS : rampHorizontalCovariantDerivative D (fun y => c y t) S x = v • H x := by
    symm
    change v • (v⁻¹ • rampHorizontalCovariantDerivative D (fun y => c y t) S x) = _
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hpair : HasDerivAt (fun y => (F.metric t).inner (c y t) (S y) (H y))
      ((F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative D (fun y => c y t) S x) (H x) +
      (F.metric t).inner (c x t) (S x)
        (rampHorizontalCovariantDerivative D (fun y => c y t) H x)) x :=
    M62.hasDerivAt_metric_pairing D (hgammaSpace x) (hS x) hHspace
  have hzero : (fun y => (F.metric t).inner (c y t) (S y) (H y)) =
      fun _ : ℝ => 0 := by
    funext y
    rw [(F.metric t).symm (c y t) (S y) (H y)]
    exact horth y
  rw [hzero] at hpair
  have hvalue := hpair.unique (hasDerivAt_const x (0 : ℝ))
  rw [hDS] at hvalue
  simp only [map_smul, smul_apply, smul_eq_mul] at hvalue
  have hcrossS : (F.metric t).inner (c x t) (S x)
      (rampHorizontalCovariantDerivative D (fun y => c y t) H x) =
        -v * m62CurvatureSquared F c t x := by
    change v * m62CurvatureSquared F c t x + _ = 0 at hvalue
    linarith
  have hcross : (F.metric t).inner (c x t) (X x)
      (rampHorizontalCovariantDerivative D (fun y => c y t) H x) =
        -v ^ 2 * m62CurvatureSquared F c t x := by
    rw [hX]
    simp only [map_smul, smul_apply, smul_eq_mul, hcrossS]
    ring
  have hcross' := (F.metric t).symm (c x t)
    (rampHorizontalCovariantDerivative D (fun y => c y t) H x) (X x)
  rw [hcross] at hcross'
  obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_ricciEvaluation D).1 (c x t)
  have hscale := A.map_smul_univ (fun _ : Fin 2 => v) (fun _ : Fin 2 => S x)
  rw [← hA, ← hA] at hscale
  have hRic : D.ricci (c x t) (X x) (X x) = v ^ 2 * m62TangentRicci F c t x := by
    rw [hX]
    simpa only [LeviCivitaData.ricciEvaluation, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, m62TangentRicci, D, S] using hscale
  have heq : (fun y => curveVelocity (fun s => c y s) t) = H :=
    funext (hc.equation t ht)
  rw [heq] at hcommute
  have hflow := M62.hasDerivAt_flow_metric_pairing F (γ := fun s => c x s)
    (Y := fun s => curveVelocity (fun y => c y s) x)
    (Z := fun s => curveVelocity (fun y => c y s) x) htF hgammaTime hXtime hXtime
  have hsq : HasDerivAt (fun s => (curveSpeed F c s x) ^ 2)
      (-2 * (m62TangentRicci F c t x + m62CurvatureSquared F c t x) * v ^ 2) t := by
    apply (hflow.congr_of_eventuallyEq
      (Eventually.of_forall (fun s => M62.speed_sq F c s x))).congr_deriv
    rw [hcommute]
    change -2 * D.ricci (c x t) (X x) (X x) +
      (F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative D (fun y => c y t) H x) (X x) +
      (F.metric t).inner (c x t) (X x)
        (rampHorizontalCovariantDerivative D (fun y => c y t) H x) = _
    rw [hcross, hcross', hRic]
    ring
  have h := hsq.sqrt (pow_ne_zero 2 hv)
  have hsqrt : (fun s => curveSpeed F c s x) =ᶠ[𝓝 t]
      (fun s => Real.sqrt (curveSpeed F c s x ^ 2)) :=
    Eventually.of_forall fun s => (Real.sqrt_sq (M62.speed_nonneg F c s x)).symm
  apply (h.congr_of_eventuallyEq hsqrt).congr_deriv
  rw [Real.sqrt_sq (M62.speed_nonneg F c t x)]
  change -2 * _ * v ^ 2 / (2 * v) = -_ * v
  field_simp

end PoincareConjecture.M63
