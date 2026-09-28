import PoincareConjecture.Proofs.M62.Lemma0_2_CurveLaws
import PoincareConjecture.Definitions.M63Ramp












set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63SpatialDerivative_time_commutator_pair [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c)
    (Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (Z : TangentSpace (𝓡 n) (c x t)) :
    let D := F.connection t
    let S := spatialUnitTangent F c t x
    let H := m62CurvatureVector F c t x
    let A := m62TangentRicci F c t x + m62CurvatureSquared F c t x
    (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62SpatialDerivative F c r (fun y => Y (y, r)) x) t) Z =
      (F.metric t).inner (c x t)
        (m62SpatialDerivative F c t (fun y =>
          rampHorizontalCovariantDerivative D (fun r => c y r)
            (fun r => Y (y, r)) t) x) Z +
      A * (F.metric t).inner (c x t)
        (m62SpatialDerivative F c t (fun y => Y (y, t)) x) Z +
      D.curvatureTensor (c x t) H S Z (Y (x, t)) -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, Y (x, t), Z] -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Y (x, t), S, Z] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, Y (x, t)] := by
  let D := F.connection t
  let v := curveSpeed F c t x
  let S := spatialUnitTangent F c t x
  let H := m62CurvatureVector F c t x
  let A := m62TangentRicci F c t x + m62CurvatureSquared F c t x
  let P : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := fun z =>
    rampHorizontalCovariantDerivative (F.connection z.2) (fun y => c y z.2)
      (fun y => Y (y, z.2)) z.1
  have hv : v ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hP := flow_pullback_space_smooth F c Y hopen
    (fun z hz => by simpa only [interior_Icc] using hz.2) hc.joint_smooth hY
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (x, r)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hPt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun r => (⟨c x r, P (x, r)⟩ : TangentBundle (𝓡 n) M)) t := by
    exact ((hP.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime
  have hvinv : HasDerivAt (fun r => (curveSpeed F c r x)⁻¹) (A * v⁻¹) t := by
    apply ((hasDerivAt_speed F c hc ht x).inv hv).congr_deriv
    change -(-A * v) / v ^ 2 = A * v⁻¹
    field_simp
  have hprod :
      rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62SpatialDerivative F c r (fun y => Y (y, r)) x) t =
      (A * v⁻¹) • P (x, t) + v⁻¹ •
        rampHorizontalCovariantDerivative D (fun r => c x r)
          (fun r => P (x, r)) t := by
    exact pullback_smul D hvinv hPt
  have hcomm := flow_pullback_curvature_pair F c Y hopen
    (fun z hz => by simpa only [interior_Icc] using hz.2) hc.joint_smooth hY hmem Z
  have hX : curveVelocity (fun y => c y t) x = v • S := by
    dsimp only [S, spatialUnitTangent, v]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hU : curveVelocity (fun r => c x r) t = H := hc.equation t ht x
  dsimp only at hcomm
  rw [hX, hU] at hcomm
  have hcurv : (F.metric t).inner (c x t)
      (D.curvature (c x t) H (v • S) (Y (x, t))) Z =
      v * D.curvatureTensor (c x t) H S Z (Y (x, t)) := by
    change D.curvatureTensor (c x t) H (v • S) Z (Y (x, t)) = _
    obtain ⟨R, hR⟩ := (M04.isSmoothCovariantTensor_riemannEvaluation D).1 (c x t)
    have hscale := R.map_smul_univ ![1, v, 1, 1] ![H, S, Z, Y (x, t)]
    have heq : (fun i : Fin 4 =>
        ![1, v, 1, 1] i • ![H, S, Z, Y (x, t)] i) =
        ![H, v • S, Z, Y (x, t)] := by
      funext i
      fin_cases i <;> simp
    rw [heq, ← hR, ← hR] at hscale
    simpa [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ] using hscale
  obtain ⟨K, hK⟩ := (M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (M04.isSmoothCovariantTensor_ricciEvaluation D)).1 (c x t)
  have hderScale (W V : Fin 3 → TangentSpace (𝓡 n) (c x t)) (i : Fin 3)
      (hi : W i = v • V i) (hj : ∀ j, j ≠ i → W j = V j) :
      D.covariantTensorDerivative D.ricciEvaluation (c x t) W =
        v * D.covariantTensorDerivative D.ricciEvaluation (c x t) V := by
    have hscale := K.map_smul_univ (fun j => if j = i then v else 1) V
    have heq : (fun j => (if j = i then v else 1) • V j) = W := by
      funext j
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        exact hi.symm
      · rw [if_neg hji, one_smul, hj j hji]
    rw [heq, ← hK, ← hK] at hscale
    have hfactor : (∏ j : Fin 3, if j = i then v else 1) = v := by
      fin_cases i <;> simp
    simpa only [hfactor, smul_eq_mul] using hscale
  have hder1 : D.covariantTensorDerivative D.ricciEvaluation (c x t)
      ![v • S, Y (x, t), Z] =
      v * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, Y (x, t), Z] := by
    apply hderScale _ _ 0
    · simp
    · intro j hj
      fin_cases j <;> simp_all
  have hder2 : D.covariantTensorDerivative D.ricciEvaluation (c x t)
      ![Y (x, t), v • S, Z] =
      v * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Y (x, t), S, Z] := by
    apply hderScale _ _ 1
    · simp
    · intro j hj
      fin_cases j <;> simp_all
  have hder3 : D.covariantTensorDerivative D.ricciEvaluation (c x t)
      ![Z, v • S, Y (x, t)] =
      v * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, Y (x, t)] := by
    apply hderScale _ _ 1
    · simp
    · intro j hj
      fin_cases j <;> simp_all
  rw [hcurv, hder1, hder2, hder3] at hcomm
  change (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62SpatialDerivative F c r (fun y => Y (y, r)) x) t) Z = _
  rw [hprod]
  simp only [m62SpatialDerivative, map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  change (A * v⁻¹) * (F.metric t).inner (c x t) (P (x, t)) Z +
      v⁻¹ * (F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative D (fun r => c x r)
          (fun r => P (x, r)) t) Z =
      v⁻¹ * (F.metric t).inner (c x t)
        (rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => rampHorizontalCovariantDerivative D (fun r => c y r)
            (fun r => Y (y, r)) t) x) Z +
      A * (v⁻¹ * (F.metric t).inner (c x t) (P (x, t)) Z) +
      D.curvatureTensor (c x t) H S Z (Y (x, t)) -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, Y (x, t), Z] -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Y (x, t), S, Z] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, Y (x, t)]
  simp only [map_sub, sub_apply] at hcomm
  apply (mul_left_cancel₀ hv)
  field_simp
  nlinarith only [hcomm]




theorem m63CurvatureVector_time_pair [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (Z : TangentSpace (𝓡 n) (c x t)) :
    let D := F.connection t
    let S := spatialUnitTangent F c t x
    let H := m62CurvatureVector F c t x
    let A := m62TangentRicci F c t x + m62CurvatureSquared F c t x
    (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62CurvatureVector F c r x) t) Z =
      (F.metric t).inner (c x t) (m63CurvatureJet F c 2 t x) Z +
      2 * A * (F.metric t).inner (c x t) H Z +
      m62ArcDerivative F c t
        (fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y) x *
        (F.metric t).inner (c x t) S Z +
      D.curvatureTensor (c x t) H S Z S -
      2 * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, S, Z] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, S] := by
  let D := F.connection t
  let S : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => spatialUnitTangent F c z.2 z.1
  let H : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62CurvatureVector F c t y
  let B : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62SpatialDerivative F c t (m62CurvatureVector F c t) y
  let A : ℝ × ℝ → ℝ := fun z =>
    m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1
  let v := curveSpeed F c t x
  have hv : v ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hspace : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hSjoint := unitTangent_joint_contMDiff F c hc
  have hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, S (y, t)⟩ : TangentBundle (𝓡 n) M)) x := by
    exact ((hSjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace
  have hBjoint := spatialDerivative_joint_contMDiff F c hc
    (fun z => m62CurvatureVector F c z.2 z.1) (curvature_joint_contMDiff F c hc)
  have hB : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, B y⟩ : TangentBundle (𝓡 n) M)) x := by
    exact ((hBjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace
  have hA : DifferentiableAt ℝ (fun y => A (y, t)) x := by
    have hAxy : ContDiffAt ℝ ∞ A (x, t) :=
      (normalization_coefficient_contDiffOn F c hc).contDiffAt (hopen.mem_nhds hmem)
    have hspaceD : DifferentiableAt ℝ (fun y : ℝ => (y, t)) x :=
      differentiableAt_id.prodMk (differentiableAt_const t)
    exact (hAxy.differentiableAt (by simp)).comp x hspaceD
  have hAS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, A (y, t) • S (y, t)⟩ : TangentBundle (𝓡 n) M)) x := by
    rw [mdifferentiableAt_totalSpace] at hS ⊢
    refine ⟨hS.1, ?_⟩
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (c x t)
    have hnear : ∀ᶠ y in 𝓝 x, c y t ∈ e.baseSet :=
      hS.1.continuousAt (e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (c x t)))
    apply (hA.mdifferentiableAt.smul hS.2).congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    change (e ⟨c y t, A (y, t) • S (y, t)⟩).2 =
      A (y, t) • (e ⟨c y t, S (y, t)⟩).2
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hy] using
      (e.continuousLinearMapAt ℝ (c y t)).map_smul (A (y, t)) (S (y, t))
  have hunit (y : ℝ) :
      rampHorizontalCovariantDerivative D (fun r => c y r)
        (fun r => S (y, r)) t = B y + A (y, t) • S (y, t) :=
    unitTangent_time_derivative F c hc ht y
  have hDx :
      rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => rampHorizontalCovariantDerivative D (fun r => c y r)
          (fun r => S (y, r)) t) x =
      rampHorizontalCovariantDerivative D (fun y => c y t) B x +
        deriv (fun y => A (y, t)) x • S (x, t) +
        A (x, t) • rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => S (y, t)) x := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => B y + A (y, t) • S (y, t)) x :=
        pullback_congr D
          (Y := fun y => rampHorizontalCovariantDerivative D (fun r => c y r)
            (fun r => S (y, r)) t)
          (Z := fun y => B y + A (y, t) • S (y, t))
          (Eventually.of_forall hunit)
      _ = _ := by
        rw [pullback_add D hB hAS, pullback_smul D hA.hasDerivAt hS]
        abel
  have hDxB : rampHorizontalCovariantDerivative D (fun y => c y t) B x =
      v • m63CurvatureJet F c 2 t x := by
    dsimp only [m63CurvatureJet, m62SpatialDerivative, B, v]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hDxS : rampHorizontalCovariantDerivative D (fun y => c y t)
      (fun y => S (y, t)) x = v • H x := by
    dsimp only [H, m62CurvatureVector, m62SpatialDerivative, S, v]
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hcomm := m63SpatialDerivative_time_commutator_pair F c hc S hSjoint ht x Z
  have hnormalized : (F.metric t).inner (c x t)
      (m62SpatialDerivative F c t (fun y =>
        rampHorizontalCovariantDerivative D (fun r => c y r)
          (fun r => S (y, r)) t) x) Z =
      (F.metric t).inner (c x t) (m63CurvatureJet F c 2 t x) Z +
      m62ArcDerivative F c t (fun y => A (y, t)) x *
        (F.metric t).inner (c x t) (S (x, t)) Z +
      A (x, t) * (F.metric t).inner (c x t) (H x) Z := by
    rw [m62SpatialDerivative, hDx, hDxB, hDxS]
    simp only [smul_add, map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
    change v⁻¹ * (v * _) + v⁻¹ * (deriv (fun y => A (y, t)) x * _) +
      v⁻¹ * (A (x, t) * (v * _)) = _
    dsimp only [m62ArcDerivative, v]
    field_simp [show curveSpeed F c t x ≠ 0 from hv]
  dsimp only at hcomm ⊢
  rw [hnormalized] at hcomm
  change (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62CurvatureVector F c r x) t) Z = _ at hcomm
  change (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => m62CurvatureVector F c r x) t) Z = _
  convert hcomm using 1
  dsimp only [D, S, H, A, m62CurvatureVector]
  ring




theorem m63CurvatureSquared_firstJet_dissipation
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (hE : M62CurveEstimates F c K0 K1 K2)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => m62CurvatureSquared F c r x) t ≤
      m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
        2 * m63CurvatureJetSquared F c 1 t x +
        4 * (m62CurvatureSquared F c t x) ^ 2 +
        m62C0 K0 K1 K2 * (m62CurvatureSquared F c t x + m62Curvature F c t x) := by
  have hsplit := spatialDerivative_norm_split F c hc ht x
  have hbound := hE.spatial_squared_bound t ht x
  change m63CurvatureJetSquared F c 1 t x = _ at hsplit
  dsimp only at hbound
  linarith only [hbound, hsplit]

end PoincareConjecture
