import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.L2Pullback
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakDerivativeLimit
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.L2







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

namespace EnergyTest

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
theorem coordinateDerivative_memLp
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) (f : EnergyTest D Ω) :
    MemLp (fun x => fderiv ℝ (fun y => f (e y)) x v) 2 (volume.restrict K) := by
  have hF : ContDiffOn ℝ ∞ (fun y => f (e y)) e.source :=
    (f.smooth.comp_contMDiffOn he).contDiffOn
  have hd : ContinuousOn (fun x => fderiv ℝ (fun y => f (e y)) x v) K :=
    ((hF.continuousOn_fderiv_of_isOpen e.open_source (by simp)).clm_apply
      continuousOn_const).mono hKs
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd
  exact MemLp.of_bound (hd.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)


def coordinateDerivativeL2
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) (f : EnergyTest D Ω) :
    Lp ℝ 2 (volume.restrict K) :=
  (coordinateDerivative_memLp e he hK hKs v f).toLp _

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
theorem coordinateDerivativeL2_ae
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) (f : EnergyTest D Ω) :
    (coordinateDerivativeL2 e he hK hKs v f : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict K] fun x => fderiv ℝ (fun y => f (e y)) x v :=
  (coordinateDerivative_memLp e he hK hKs v f).coeFn_toLp


def coordinateDerivativeLinear
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    EnergyTest D Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun := coordinateDerivativeL2 e he hK hKs v
  map_add' f h := by
    apply Lp.ext
    filter_upwards [coordinateDerivativeL2_ae e he hK hKs v (f + h),
      coordinateDerivativeL2_ae e he hK hKs v f,
      coordinateDerivativeL2_ae e he hK hKs v h,
      Lp.coeFn_add (coordinateDerivativeL2 e he hK hKs v f)
        (coordinateDerivativeL2 e he hK hKs v h),
      ae_restrict_mem hK.measurableSet] with x hsum hf hh hadd hx
    rw [hsum, hadd, Pi.add_apply, hf, hh]
    have hf' := ((f.smooth.comp_contMDiffOn he).contDiffOn.contDiffAt
      (e.open_source.mem_nhds (hKs hx))).differentiableAt (by simp)
    have hh' := ((h.smooth.comp_contMDiffOn he).contDiffOn.contDiffAt
      (e.open_source.mem_nhds (hKs hx))).differentiableAt (by simp)
    simp only [coe_add]
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
      (fderiv_add hf' hh')
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coordinateDerivativeL2_ae e he hK hKs v (c • f),
      coordinateDerivativeL2_ae e he hK hKs v f,
      Lp.coeFn_smul c (coordinateDerivativeL2 e he hK hKs v f),
      ae_restrict_mem hK.measurableSet] with x hsmul hf hmul hx
    simp only [RingHom.id_apply]
    rw [hsmul, hmul, Pi.smul_apply, hf]
    have hf' := ((f.smooth.comp_contMDiffOn he).contDiffOn.contDiffAt
      (e.open_source.mem_nhds (hKs hx))).differentiableAt (by simp)
    simp only [coe_smul, smul_eq_mul]
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
      (fderiv_const_mul hf' c)


theorem exists_coordinateDerivative_bound
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, ∀ f : EnergyTest D Ω,
      ‖coordinateDerivativeLinear e he hK hKs v f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_sq_coordinate_derivative_le_energy
    (D := D) (Ω := Ω) e he hei hK hKs v
  refine ⟨Real.sqrt C, fun f => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f))).mp
  change ‖(coordinateDerivative_memLp e he hK hKs v f).toLp _‖ ^ 2 ≤ _
  rw [Poincare.Analysis.Sobolev.norm_toLp_sq_eq_integral, mul_pow, Real.sq_sqrt hC.le]
  exact hbound f


def coordinateDerivativeCLM
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    EnergyTest D Ω →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (coordinateDerivativeLinear e he hK hKs v).mkContinuous
    (exists_coordinateDerivative_bound e he hei hK hKs v).choose
    (exists_coordinateDerivative_bound e he hei hK hKs v).choose_spec

end EnergyTest


def coordinateDerivative
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    H1Zero D Ω →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  Poincare.Analysis.Dirichlet.completionMap
    (EnergyTest.coordinateDerivativeCLM e he hei hK hKs v)

@[simp] theorem coordinateDerivative_coe
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) (f : EnergyTest D Ω) :
    coordinateDerivative e he hei hK hKs v (f : H1Zero D Ω) =
      EnergyTest.coordinateDerivativeL2 e he hK hKs v f := by
  exact Poincare.Analysis.Dirichlet.completionMap_coe _ _



def localCoordinateDerivative
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K S : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hSK : S ⊆ K) (v : EuclideanSpace ℝ (Fin n)) :
    H1Zero D Ω →L[ℝ] Lp ℝ 2 (volume.restrict S) :=
  (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono hSK (le_refl volume))).comp
      (coordinateDerivative e he hei hK hKs v)

theorem localCoordinateDerivative_coe_ae
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K S : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hSK : S ⊆ K) (v : EuclideanSpace ℝ (Fin n))
    (f : EnergyTest D Ω) :
    (localCoordinateDerivative e he hei hK hKs hSK v (f : H1Zero D Ω) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict S]
        fun x => fderiv ℝ (fun y => f (e y)) x v := by
  have hrestrict : volume.restrict S ≤ volume.restrict K := Measure.restrict_mono hSK le_rfl
  change (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using hrestrict)
      (coordinateDerivative e he hei hK hKs v (f : H1Zero D Ω)) :
        EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict S] _
  rw [coordinateDerivative_coe]
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using hrestrict) _).trans
      ((EnergyTest.coordinateDerivativeL2_ae e he hK hKs v f).filter_mono (ae_mono hrestrict))



theorem localCoordinateDerivative_weak
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hO : IsOpen O)
    (u : H1Zero D Ω) (i : Fin n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, (toL2 D Ω u) (e x) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      -(∫ x in O, localCoordinateDerivative e he hei hK hKs hOK
        (EuclideanSpace.single i 1) u x * φ x) := by
  let P := g.localL2Pullback e he hei hK hKs hOK
  let T := localCoordinateDerivative (D := D) (Ω := Ω) e he hei hK hKs hOK
    (EuclideanSpace.single i 1)
  obtain ⟨f, hf, hfL2⟩ := exists_energyTest_approximation u
  have hP : Tendsto (fun k => P (testToL2 D Ω (f k))) atTop (𝓝 (P (toL2 D Ω u))) :=
    P.continuous.continuousAt.tendsto.comp hfL2
  have hT : Tendsto (fun k => T (f k : H1Zero D Ω)) atTop (𝓝 (T u)) :=
    T.continuous.continuousAt.tendsto.comp hf
  have hweak := Poincare.Analysis.Elliptic.weak_partial_of_tendsto_L2 i hP hT
    (fun k ψ hψ hψc hψs => ?_) φ hφ hc hs
  · have hae := g.localL2Pullback_ae e he hei hK hKs hOK (toL2 D Ω u)
    have heq : (∫ x in O, P (toL2 D Ω u) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, (toL2 D Ω u) (e x) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact hae.mul (EventuallyEq.rfl)
    exact heq.symm.trans hweak
  · have haeP := g.localL2Pullback_ae e he hei hK hKs hOK (testToL2 D Ω (f k))
    have haeF : (fun x => testToL2 D Ω (f k) (e x)) =ᵐ[volume.restrict O]
        fun x => f k (e x) := by
      apply Filter.EventuallyEq.filter_mono _ (ae_mono (Measure.restrict_mono hOK le_rfl))
      exact g.ae_comp_on_compact e he hei hK hKs (f k).memLp.coeFn_toLp
    have haeT := localCoordinateDerivative_coe_ae e he hei hK hKs hOK
      (EuclideanSpace.single i 1) (f k)
    calc
      _ = ∫ x in O, f k (e x) * fderiv ℝ ψ x (EuclideanSpace.single i 1) :=
        integral_congr_ae ((haeP.trans haeF).mul EventuallyEq.rfl)
      _ = -(∫ x in O, fderiv ℝ (fun y => f k (e y)) x
          (EuclideanSpace.single i 1) * ψ x) :=
        Poincare.Analysis.Elliptic.integral_mul_partial_test hO
          (((f k).smooth.comp_contMDiffOn he).contDiffOn.mono (hOK.trans hKs))
          (EuclideanSpace.single i 1) hψ hψc hψs
      _ = _ := congrArg Neg.neg (integral_congr_ae (haeT.mul EventuallyEq.rfl)).symm

end PoincareConjecture.LeviCivitaData.Dirichlet
