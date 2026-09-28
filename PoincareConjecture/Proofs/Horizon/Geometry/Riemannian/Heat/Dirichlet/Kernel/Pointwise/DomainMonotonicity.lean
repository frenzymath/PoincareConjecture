import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.TestOrder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Order








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω1 Ω2 : Set M}
  (D : LeviCivitaData g)

omit [NeZero n] in
private theorem integral_mul_test_restrict_domain (hΩ2 : MeasurableSet Ω2)
    (h12 : Ω1 ⊆ Ω2) (φ : EnergyTest D Ω1) (F : M → ℝ) :
    (∫ y in Ω2, F y * φ y ∂g.volumeMeasure) =
      ∫ y in Ω1, F y * φ y ∂g.volumeMeasure := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ2 h12
  intro y hy
  have hφ : φ y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hy.2 (φ.support_subset h))
  simp only [hφ, mul_zero]

private theorem heat_test_domain_le
    (S1 : Poincare.Manifold.SmoothDomain n Ω1)
    (S2 : Poincare.Manifold.SmoothDomain n Ω2)
    (h12 : Ω1 ⊆ Ω2) (φ1 : EnergyTest D Ω1) (φ2 : EnergyTest D Ω2)
    (hφeq : ∀ x : M, φ1 x = φ2 x) (hφ : ∀ x : M, 0 ≤ φ1 x)
    (t : ℝ) (ht : 0 < t) (x : M) (hx : x ∈ Ω1) :
    heatPowerContinuous D S1 0 t ht (toDomainL2 D Ω1 (φ1 : H1Zero D Ω1)) x ≤
      heatPowerContinuous D S2 0 t ht (toDomainL2 D Ω2 (φ2 : H1Zero D Ω2)) x := by
  obtain ⟨F1, hF1, hinit1, hpos1⟩ := exists_continuous_heat_test D S1 φ1
  obtain ⟨F2, hF2, hinit2, hpos2⟩ := exists_continuous_heat_test D S2 φ2
  have hc1 : Continuous (fun p : M × ℝ => F1 p.2 p.1) :=
    continuous_eval.comp ((hF1.comp continuous_snd).prodMk continuous_fst)
  have hc2 : Continuous (fun p : M × ℝ => F2 p.2 p.1) :=
    continuous_eval.comp ((hF2.comp continuous_snd).prodMk continuous_fst)
  have hboundary (y : M) (_hy : y ∈ closure Ω1) (hyo : y ∉ Ω1)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : F1 s y ≤ F2 s y := by
    by_cases hsp : 0 < s
    · rw [hpos1 s hsp, hpos2 s hsp,
        heatPowerContinuousTime_of_pos D S1 0 hsp,
        heatPowerContinuousTime_of_pos D S2 0 hsp,
        heatPowerContinuous_zero_outside D S1 0 s hsp _ y hyo]
      exact heatPowerContinuous_test_nonneg D S2 φ2
        (fun z => by rw [← hφeq z]; exact hφ z) s hsp y
    · have hs0 : s = 0 := le_antisymm (not_lt.mp hsp) hs.1
      rw [hs0, hinit1, hinit2, hφeq]
  have hcompare := le_of_subsolution_supersolution D S1.isOpen S1.isCompact_closure
    (F := fun y s => F1 s y) (G := fun y s => F2 s y)
    (F' := fun y s => D.laplacian (F1 s : M → ℝ) y)
    (G' := fun y s => D.laplacian (F2 s : M → ℝ) y)
    (a := 0) (b := t) hc1.continuousOn hc2.continuousOn
    (fun s hs => contMDiffOn_heat_test_extension D S1 φ1 F1 hpos1 s hs.1)
    (fun s hs => (contMDiffOn_heat_test_extension D S2 φ2 F2 hpos2 s hs.1).mono h12)
    (fun y hy s hs =>
      (hasDerivAt_heat_test_extension D S1 φ1 F1 hpos1 s hs.1 y hy).hasDerivWithinAt)
    (fun y hy s hs =>
      (hasDerivAt_heat_test_extension D S2 φ2 F2 hpos2 s hs.1 y (h12 hy)).hasDerivWithinAt)
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) hboundary
    (fun y _ => by rw [hinit1, hinit2, hφeq])
  have h := hcompare x (subset_closure hx) t ⟨ht.le, le_rfl⟩
  rw [hpos1 t ht, hpos2 t ht,
    heatPowerContinuousTime_of_pos D S1 0 ht,
    heatPowerContinuousTime_of_pos D S2 0 ht] at h
  exact h


theorem heatKernelContinuous_domain_mono
    (S1 : Poincare.Manifold.SmoothDomain n Ω1)
    (S2 : Poincare.Manifold.SmoothDomain n Ω2)
    (h12 : Ω1 ⊆ Ω2) (t : ℝ) (ht : 0 < t)
    (x y : M) (hx : x ∈ Ω1) (hy : y ∈ Ω1) :
    heatKernelContinuous D S1 t ht x y ≤ heatKernelContinuous D S2 t ht x y := by
  let K1 : M → ℝ := heatKernelContinuous D S1 t ht x
  let K2 : M → ℝ := heatKernelContinuous D S2 t ht x
  have hK1 : Continuous K1 := by
    simpa only [K1, Function.comp_def, id_eq] using
      (continuous_heatKernelContinuous D S1 t ht).comp
        (continuous_const.prodMk continuous_id)
  have hK2 : Continuous K2 := by
    simpa only [K2, Function.comp_def, id_eq] using
      (continuous_heatKernelContinuous D S2 t ht).comp
        (continuous_const.prodMk continuous_id)
  have hdiff : ∀ z ∈ Ω1, 0 ≤ K2 z - K1 z := by
    apply nonneg_of_integral_mul_test_nonneg (D := D) S1.isOpen (hK2.sub hK1)
    intro φ hφ
    let φ2 : EnergyTest D Ω2 :=
      ⟨(φ : M → ℝ), φ.smooth, φ.hasCompactSupport, φ.support_subset.trans h12⟩
    have hcomp := heat_test_domain_le D S1 S2 h12 φ φ2 (fun _ => rfl) hφ t ht x hx
    rw [← integral_heatKernelContinuous_test D S1 t ht x φ,
      ← integral_heatKernelContinuous_test D S2 t ht x φ2] at hcomp
    change (∫ z in Ω1, K1 z * φ z ∂g.volumeMeasure) ≤
      ∫ z in Ω2, K2 z * φ z ∂g.volumeMeasure at hcomp
    rw [integral_mul_test_restrict_domain D S2.isOpen.measurableSet h12 φ K2] at hcomp
    have hi1 : Integrable (fun z => K1 z * φ z) (g.volumeMeasure.restrict Ω1) :=
      ((hK1.mul φ.smooth.continuous).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_left).restrict
    have hi2 : Integrable (fun z => K2 z * φ z) (g.volumeMeasure.restrict Ω1) :=
      ((hK2.mul φ.smooth.continuous).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_left).restrict
    change 0 ≤ ∫ z in Ω1, (K2 z - K1 z) * φ z ∂g.volumeMeasure
    simp_rw [sub_mul]
    rw [integral_sub hi2 hi1]
    exact sub_nonneg.mpr hcomp
  exact sub_nonneg.mp (hdiff y hy)

end PoincareConjecture.LeviCivitaData.Dirichlet
