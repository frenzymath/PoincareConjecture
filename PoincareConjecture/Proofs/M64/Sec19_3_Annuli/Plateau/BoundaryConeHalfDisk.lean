import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeGreenIntegrability
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeFluxIntegral
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeDisk














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareConjecture.M64BoundaryCone

open M65Interior M65Boundary

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]




theorem halfCone_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : C → E}
    {v d : ℝ → C} {v0 : C}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) :
    MemLp (coneDiskMap g r v0 v x) 2
        (volume.restrict (closedBall x r ∩ {z | x 1 ≤ z 1})) ∧
      ∀ i, MemLp (coneDiskField g r v0 v d x i) 2
        (volume.restrict (closedBall x r ∩ {z | x 1 ≤ z 1})) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (0 : ℝ) Real.pi
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hc := (cone_reconstruction_continuous hr hρ hv hg h0 hvb).1
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  have hm : MemLp (fun p : ℝ × ℝ => g (coneCoordinates r v0 v p.1 p.2)) 2
      (volume.restrict S) := by
    apply MemLp.of_bound (hc.aestronglyMeasurable hS.measurableSet) B
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
    exact hB p hp
  exact ⟨memLp_halfPolarCoordinates hm x, fun i => memLp_halfPolarCoordinates
    (coneCartesianField_memLp hr hρ hK hv hg h0 hvb hd hD i) x⟩





theorem halfCone_green_rectangle [CompleteSpace C] [ProperSpace C] {g : C → ℝ}
    {v d : ℝ → C} {v0 : C}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ t ∈ Icc (0 : ℝ) Real.pi, ∀ u ∈ Icc (0 : ℝ) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    (∫ p in Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) Real.pi,
      p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
        g (coneCoordinates r v0 v p.1 p.2) *
          fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i))) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i) +
      ∫ s in (0 : ℝ)..r,
        coneAngularFlux g r v0 v x test i s Real.pi -
          coneAngularFlux g r v0 v x test i s 0 := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (0 : ℝ) Real.pi
  let R (p : ℝ × ℝ) := deriv (fun s => coneRadialFlux g r v0 v x test i s p.2) p.1
  let Q (p : ℝ × ℝ) := deriv (fun θ => coneAngularFlux g r v0 v x test i p.1 θ) p.2
  have hvc : ContinuousOn v (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hv.continuousOn
  have hI : IntervalIntegrable d volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr
      (hd.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hR : IntegrableOn R S :=
    (coneRadialFlux_deriv_continuous hr hρ hvc hg h0 hvb x test ht i).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hQ : IntegrableOn Q S :=
    coneAngularFlux_deriv_integrable hr hρ hK Real.pi_pos hvc hg h0 hvb hd hinc hD x test ht i
  have hprod : ∀ᵐ p ∂volume.restrict S, HasDerivAt v (d p.2) p.2 := by
    have h := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (0 : ℝ) r))).ae (increment_ae_hasDerivAt Real.pi_pos hI hinc)
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have heq : (fun p : ℝ × ℝ =>
      p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
        g (coneCoordinates r v0 v p.1 p.2) *
          fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)))
      =ᵐ[volume.restrict S] fun p => R p + Q p := by
    filter_upwards [hprod, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
      with p hp hpS
    have hm : coneCoordinates r v0 v p.1 p.2 ∈
        ball (0 : C) (2 * ρ) :=
      (closedBall_subset_ball (by linarith))
        (coneCoordinates_mem_closedBall hr h0 (hvb hpS.2) hpS.1)
    exact (coneFlux_derivative_sum r v0 v d x test i p.1 p.2 hp
      ((hg.contDiffAt (isOpen_ball.mem_nhds hm)).differentiableAt one_ne_zero)
      (ht.differentiable one_ne_zero _)).symm
  have hRp : Integrable R
      ((volume.restrict (Icc (0 : ℝ) r)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hQp : Integrable Q
      ((volume.restrict (Icc (0 : ℝ) r)).prod (volume.restrict (Icc (0 : ℝ) Real.pi))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hrad : (∫ p in S, R p) = r * ∫ θ in (0 : ℝ)..Real.pi,
      g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i := by
    have hf := integral_prod_symm R hRp
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    calc
      _ = ∫ θ in Icc (0 : ℝ) Real.pi, ∫ s in Icc (0 : ℝ) r, R (s, θ) := hf
      _ = ∫ θ in Icc (0 : ℝ) Real.pi,
          r * (g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro θ hθ
        dsimp only
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
        change (∫ s in (0 : ℝ)..r,
          deriv (fun q => coneRadialFlux g r v0 v x test i q θ) s) = _
        rw [coneRadialFlux_integral_deriv v hr hρ hg h0 θ (hvb hθ) x test ht i]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have hang : (∫ p in S, Q p) = ∫ s in (0 : ℝ)..r,
      coneAngularFlux g r v0 v x test i s Real.pi -
        coneAngularFlux g r v0 v x test i s 0 := by
    have hf := integral_prod Q hQp
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hf
    calc
      _ = ∫ s in Icc (0 : ℝ) r, ∫ θ in Icc (0 : ℝ) Real.pi, Q (s, θ) := hf
      _ = ∫ s in Icc (0 : ℝ) r,
          coneAngularFlux g r v0 v x test i s Real.pi -
            coneAngularFlux g r v0 v x test i s 0 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
        exact (coneAngularFlux_AC hr hρ Real.pi_pos hv hg h0 hvb hI hinc
          hs x test ht i).integral_deriv_eq_sub
      _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
  change (∫ p in S, _) = _
  rw [integral_congr_ae heq, integral_add hR hQ, hrad, hang]





theorem halfCone_green [CompleteSpace C] [ProperSpace C] {g : C → ℝ}
    {v d : ℝ → C} {v0 : C}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ t ∈ Icc (0 : ℝ) Real.pi, ∀ u ∈ Icc (0 : ℝ) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    IntegrableOn (fun z => coneDiskField g r v0 v d x i z * test z +
      coneDiskMap g r v0 v x z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (closedBall x r ∩ {z | x 1 ≤ z 1}) ∧
    (∫ z in closedBall x r ∩ {z | x 1 ≤ z 1},
      coneDiskField g r v0 v d x i z * test z + coneDiskMap g r v0 v x z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        g (v θ) * test (polarPlane x (r, θ)) * Proofs.M58.angularPoint θ i) +
      ∫ s in (0 : ℝ)..r,
        coneAngularFlux g r v0 v x test i s Real.pi -
          coneAngularFlux g r v0 v x test i s 0 := by
  have hvc : ContinuousOn v (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hv.continuousOn
  have hL := halfCone_memLp hr hρ hK hvc hg h0 hvb hd hD x
  have hcompact : IsCompact (closedBall x r ∩ {z : LoopPlane | x 1 ≤ z 1}) :=
    (isCompact_closedBall x r).inter_right (isClosed_le continuous_const (by fun_prop))
  let : IsFiniteMeasure (volume.restrict (closedBall x r ∩ {z : LoopPlane | x 1 ≤ z 1})) :=
    isFiniteMeasure_restrict.mpr hcompact.measure_lt_top.ne
  have hdt : Continuous (fun z =>
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
    (ht.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1L : IntegrableOn (coneDiskField g r v0 v d x i)
      (closedBall x r ∩ {z | x 1 ≤ z 1}) :=
    (hL.2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h0L : IntegrableOn (coneDiskMap g r v0 v x)
      (closedBall x r ∩ {z | x 1 ≤ z 1}) :=
    hL.1.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  refine ⟨(h1L.mul_continuousOn ht.continuous.continuousOn hcompact).add
    (h0L.mul_continuousOn hdt.continuousOn hcompact), ?_⟩
  have he : (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) Real.pi) =ᵐ[volume]
      Ioc (0 : ℝ) r ×ˢ Ioo (0 : ℝ) Real.pi :=
    (Measure.set_prod_ae_eq (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))
      (Ioo_ae_eq_Icc (α := ℝ) (μ := volume))).symm
  rw [halfDisk_integral_polar]
  calc
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (0 : ℝ) Real.pi,
        p.1 * (coneDiskField g r v0 v d x i (polarPlane x p) * test (polarPlane x p) +
          coneDiskMap g r v0 v x (polarPlane x p) *
            fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
      setIntegral_congr_set he
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (0 : ℝ) Real.pi,
        p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
          g (coneCoordinates r v0 v p.1 p.2) *
            fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      have hpt : p ∈ polarCoord.target := ⟨hp.1.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      simp only [coneDiskField_polar g r v0 v d x i hpt, coneDiskMap_polar g r v0 v x hpt]
    _ = ∫ p in Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) Real.pi,
        p.1 * (coneCartesianField g r v0 v d p.1 p.2 i * test (polarPlane x p) +
          g (coneCoordinates r v0 v p.1 p.2) *
            fderiv ℝ test (polarPlane x p) (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
      setIntegral_congr_set he.symm
    _ = _ := halfCone_green_rectangle hr hρ hK hv hg h0 hvb hd hinc hD x test ht i




theorem halfCone_derivativeEnergy_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : C → E}
    {v d : ℝ → C} {v0 : C}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hD : ∀ y ∈ closedBall (0 : C) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) :
    IntegrableOn (fun z => ∑ i : Fin 2, ‖coneDiskField g r v0 v d x i z‖ ^ 2)
      (closedBall x r ∩ {z | x 1 ≤ z 1}) ∧
    (∫ z in closedBall x r ∩ {z | x 1 ≤ z 1},
      ∑ i : Fin 2, ‖coneDiskField g r v0 v d x i z‖ ^ 2) ≤
      (K ^ 2 / 2) * ∫ θ in Icc (0 : ℝ) Real.pi, (‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (0 : ℝ) Real.pi
  let A (θ : ℝ) := ‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2
  let c := (r⁻¹) ^ 2 * K ^ 2
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hA : IntegrableOn A (Icc (0 : ℝ) Real.pi) :=
    (((hv.sub continuousOn_const).norm.pow 2).integrableOn_compact isCompact_Icc).add
      ((memLp_two_iff_integrable_sq_norm hd.1).mp hd)
  have hfields : IntegrableOn
      (fun p : ℝ × ℝ => ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2) S := by
    apply integrable_finsetSum
    intro i _
    have hi := coneCartesianField_memLp hr hρ hK hv hg h0 hvb hd hD i
    exact (memLp_two_iff_integrable_sq_norm hi.1).mp hi
  have hweighted : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2) S :=
    IntegrableOn.continuousOn_mul continuous_fst.continuousOn hfields hS
  have hmajor : IntegrableOn (fun p : ℝ × ℝ => p.1 * (c * A p.2)) S := by
    have hrad : IntegrableOn (fun s : ℝ => s) (Icc (0 : ℝ) r) :=
      continuous_id.continuousOn.integrableOn_compact isCompact_Icc
    have h := hrad.mul_prod (hA.const_mul c)
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  have hbound : (∫ p in S,
      p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2) ≤
        ∫ p in S, p.1 * (c * A p.2) := by
    apply integral_mono_ae hweighted hmajor
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
    exact mul_le_mul_of_nonneg_left
      (coneCartesianField_norm_sq_le g r v0 v d p.1 p.2
        (hD _ (coneCoordinates_mem_closedBall hr h0 (hvb hp.2) hp.1))) hp.1.1
  have hmajorEq : (∫ p in S, p.1 * (c * A p.2)) =
      (K ^ 2 / 2) * ∫ θ in Icc (0 : ℝ) Real.pi, A θ := by
    have hrad : (∫ s in Icc (0 : ℝ) r, s) = r ^ 2 / 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le, integral_id]
      ring
    change (∫ p in Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) Real.pi, p.1 * (c * A p.2)) = _
    rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun s : ℝ => s) (fun θ => c * A θ),
      hrad, integral_const_mul]
    dsimp only [c]
    field_simp
  refine ⟨?_, ?_⟩
  · apply integrable_finsetSum
    intro i _
    have hi := (halfCone_memLp hr hρ hK hv hg h0 hvb hd hD x).2 i
    exact (memLp_two_iff_integrable_sq_norm hi.1).mp hi
  have he : (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) Real.pi) =ᵐ[volume]
      Ioc (0 : ℝ) r ×ˢ Ioo (0 : ℝ) Real.pi :=
    (Measure.set_prod_ae_eq (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))
      (Ioo_ae_eq_Icc (α := ℝ) (μ := volume))).symm
  rw [halfDisk_integral_polar]
  calc
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (0 : ℝ) Real.pi,
        p.1 * ∑ i : Fin 2, ‖coneDiskField g r v0 v d x i (polarPlane x p)‖ ^ 2 :=
      setIntegral_congr_set he
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (0 : ℝ) Real.pi,
        p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2 := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      have hpt : p ∈ polarCoord.target := ⟨hp.1.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      simp only [coneDiskField_polar g r v0 v d x _ hpt]
    _ = ∫ p in S,
        p.1 * ∑ i : Fin 2, ‖coneCartesianField g r v0 v d p.1 p.2 i‖ ^ 2 :=
      setIntegral_congr_set he.symm
    _ ≤ _ := hbound.trans_eq hmajorEq

end PoincareConjecture.M64BoundaryCone
