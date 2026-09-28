import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RawAnnulusObservedLTrace
import PoincareConjecture.Proofs.M64.Mathlib.InteriorCurveTraces
import PoincareConjecture.Proofs.M64.Mathlib.VectorIntegralAbsoluteContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamWeakExtension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityCharts
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane}
  {c0 c1 : ℝ → M} {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "E" => EuclideanSpace ℝ (Fin m)

open Poincare.Analysis.Sobolev.Weak

local instance : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
  ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne

theorem interiorCurve_horizontal_fiber_data
    {f d : LoopPlane → E} (hd2 : MemLp d 2 (volume.restrict S))
    (hdeq : d =ᵐ[volume.restrict S]
      (fun p => fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1))) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      s ∈ Ioo (0 : ℝ) 1 ∧
      IntegrableOn (fun x => d (annulusPoint x s))
        (Icc (0 : ℝ) curvePeriod) volume ∧
      (∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod),
        d (annulusPoint x s) =
          fderiv ℝ f (annulusPoint x s)
            (EuclideanSpace.single (0 : Fin 2) 1)) := by
  have hd : Integrable (d : LoopPlane → E) (volume.restrict S) :=
    hd2.integrable (by norm_num)
  have hprod := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hd
  have hdeqprod := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae hdeq
  have hdeqfib := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hdeqprod)
  have hinter : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      s ∈ Ioo (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc
      (μ := (volume : Measure ℝ)))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hprod.prod_left_ae, hdeqfib, hinter]
    with s hds hxe hsinter
  have hds' : IntegrableOn (fun x => d (annulusPoint x s))
      (Icc (0 : ℝ) curvePeriod) volume := by
    change IntegrableOn (fun x => d (annulusPoint x s))
      (Icc (0 : ℝ) curvePeriod) volume at hds
    exact hds
  have hxe' : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod),
      d (annulusPoint x s) =
        fderiv ℝ f (annulusPoint x s)
          (EuclideanSpace.single (0 : Fin 2) 1) := by
    simpa only [Function.comp_def, Prod.swap] using hxe
  exact ⟨hsinter, hds', hxe'⟩

private theorem interiorCurve_horizontal_integral_absolutelyContinuous
    {d : ℝ → E} (hdi : IntervalIntegrable d volume 0 curvePeriod) :
    AbsolutelyContinuousOnInterval
      (fun x => ∫ t in (0 : ℝ)..x, d t) 0 curvePeriod := by
  exact intervalIntegral_vector_absolutelyContinuous hdi left_mem_uIcc

private theorem interiorCurve_horizontal_integral_zero
    {d : ℝ → E}
    (hzero : (∫ x in Icc (0 : ℝ) curvePeriod, d x) = 0) :
    (∫ t in (0 : ℝ)..curvePeriod, d t) = 0 := by
  rw [intervalIntegral.integral_of_le (by unfold curvePeriod; positivity),
    ← integral_Icc_eq_integral_Ioc]
  exact hzero

theorem interiorCurve_horizontal_primitive
    {f d : ℝ → E}
    (hder : ∀ x ∈ Ioo (0 : ℝ) curvePeriod,
      HasDerivAt f (d x) x)
    (hdi : IntervalIntegrable d volume 0 curvePeriod)
    (hzero : (∫ x in Icc (0 : ℝ) curvePeriod, d x) = 0) :
    ∃ F : ℝ → E,
      AbsolutelyContinuousOnInterval F 0 curvePeriod ∧
      EqOn F f (Ioo (0 : ℝ) curvePeriod) ∧
      (∀ x : ℝ, F x = F 0 + ∫ t in (0 : ℝ)..x, d t) ∧
      F 0 = F curvePeriod := by
  obtain ⟨c, hc⟩ := interiorCurve_exists_primitive
    (a := (0 : ℝ)) (b := curvePeriod) (f := f) (d := d)
    (by unfold curvePeriod; positivity) hder hdi
  let F : ℝ → E := fun x => c + ∫ t in (0 : ℝ)..x, d t
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 curvePeriod :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  have hF : AbsolutelyContinuousOnInterval F 0 curvePeriod :=
    hconst.add (interiorCurve_horizontal_integral_absolutelyContinuous hdi)
  have hzero' : (∫ t in (0 : ℝ)..curvePeriod, d t) = 0 :=
    interiorCurve_horizontal_integral_zero hzero
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [F] using (hc x hx).symm
  · intro x
    simp only [F, intervalIntegral.integral_same, add_zero]
  · have hF0 : F 0 = c := by simp only [F, intervalIntegral.integral_same, add_zero]
    have hFT : F curvePeriod = c := by simp only [F, hzero', add_zero]
    exact hF0.trans hFT.symm

theorem interiorCurve_horizontal_seam_trace
    {f d : LoopPlane → E} (hd2 : MemLp d 2 (volume.restrict S))
    (hfs : ContDiffOn ℝ 1 f S)
    (hdeq : d =ᵐ[volume.restrict S]
      (fun p => fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)))
    (hseam : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      (∫ x in Icc (0 : ℝ) curvePeriod, d (annulusPoint x s)) = 0) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ∃ F : ℝ → E,
        AbsolutelyContinuousOnInterval F 0 curvePeriod ∧
        (∀ x ∈ Ioo (0 : ℝ) curvePeriod,
          F x = f (annulusPoint x s)) ∧
        (∀ x : ℝ, F x = F 0 + ∫ t in (0 : ℝ)..x,
          fderiv ℝ f (annulusPoint t s)
            (EuclideanSpace.single (0 : Fin 2) 1)) ∧
        F 0 = F curvePeriod := by
  have hdata := interiorCurve_horizontal_fiber_data (f := f) (d := d) hd2 hdeq
  filter_upwards [hdata, hseam] with s ⟨hsinter, hds, hxe⟩ hs
  have hdf : IntegrableOn
      (fun x => fderiv ℝ f (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1))
      (Icc (0 : ℝ) curvePeriod) volume := hds.congr hxe
  have hdi : IntervalIntegrable
      (fun x => fderiv ℝ f (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1)) volume 0 curvePeriod := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by unfold curvePeriod; positivity)).mpr hdf
  have hseam' : (∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ f (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1)) = 0 := by
    calc
      _ = ∫ x in Icc (0 : ℝ) curvePeriod, d (annulusPoint x s) := by
        apply integral_congr_ae
        exact hxe.mono fun x hx => hx.symm
      _ = 0 := hs
  have hder (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) curvePeriod) :
      HasDerivAt (fun y => f (annulusPoint y s))
        (fderiv ℝ f (annulusPoint x s)
          (EuclideanSpace.single (0 : Fin 2) 1)) x := by
    have hp : annulusPoint x s ∈ S :=
      (m64AnnulusInterior_coordinates _).mpr
        ⟨hx.1, hx.2, hsinter.1, hsinter.2⟩
    exact ((hfs.contDiffAt (isOpen_interior.mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)
  obtain ⟨F, hF, hEq, hformula, hends⟩ :=
    interiorCurve_horizontal_primitive
      (f := fun x => f (annulusPoint x s))
      (d := fun x => fderiv ℝ f (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1)) hder hdi hseam'
  exact ⟨F, hF, hEq, hformula, hends⟩

theorem M64FreeWeakPhaseAnnulus.raw_equal_horizontal_seam_traces
    (L : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ∃ F : ℝ → E,
        AbsolutelyContinuousOnInterval F 0 curvePeriod ∧
        (∀ x ∈ Ioo (0 : ℝ) curvePeriod,
          F x = e (L.annulus.map (annulusPoint x s))) ∧
        (∀ x : ℝ, F x = F 0 + ∫ t in (0 : ℝ)..x,
          fderiv ℝ (e ∘ L.annulus.map) (annulusPoint t s)
            (EuclideanSpace.single (0 : Fin 2) 1)) ∧
        F 0 = F curvePeriod := by
  simpa only [Function.comp_def] using
    (interiorCurve_horizontal_seam_trace
      (f := fun p => e (L.annulus.map p))
      (d := (L.annulus.column 0 : LoopPlane → E))
      (hd2 := Lp.memLp (L.annulus.column 0))
      (hfs := by
        intro p hp
        exact (contMDiffAt_iff_contDiffAt.mp ((he _).comp p
          (hA.contMDiffAt (isOpen_interior.mem_nhds hp)))).contDiffWithinAt)
      (hdeq := by
        simpa only [Function.comp_def] using
          (L.annulus.classical_columns_of_contMDiffOn he hA 0))
      (hseam := L.annulus.angular_column_integral_eq_zero))

theorem M64FreeWeakPhaseAnnulus.raw_seam_reader_weak_partial
    (L : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    {k' : ℕ} (J : E →L[ℝ] EuclideanSpace ℝ (Fin k'))
    (i : Fin 2) (j : Fin k') :
    HasWeakPartialDeriv i
      (fun p => J (m64AnnulusSeamExtend
        (L.annulus.column i : LoopPlane → E) p) j)
      (fun p => J (e (m64AnnulusSeamExtend L.annulus.map p)) j) O := by
  exact m64WeakPartial_comp_linear L.annulus.seam_extension_memLp.1
    (L.annulus.seam_extension_memLp.2 i)
    (L.annulus.seam_extension_weak_partial i) J j

theorem M64FreeWeakPhaseAnnulus.raw_local_chart_columns
    (L : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S)
    {a : LoopPlane} (ha : a ∈ S) :
    ∃ (b : M) (K : E →L[ℝ] EuclideanSpace ℝ (Fin n)) (rho : ℝ),
      0 < rho ∧ Metric.closedBall a rho ⊆ S ∧
      (∀ p ∈ Metric.closedBall a rho,
        L.annulus.map p ∈ (extChartAt (𝓡 n) b).source ∧
          K (e (L.annulus.map p)) =
            extChartAt (𝓡 n) b (L.annulus.map p)) ∧
      ContinuousOn (fun p => K (e (L.annulus.map p)))
        (Metric.closedBall a rho) ∧
      MemLp (fun p => K (e (L.annulus.map p))) 2
        (volume.restrict (Metric.ball a rho)) ∧
      (∀ i, MemLp (fun p => K (L.annulus.column i p)) 2
        (volume.restrict (Metric.ball a rho))) ∧
      ∀ i j, HasWeakPartialDeriv i
        (fun p => K (L.annulus.column i p) j)
        (fun p => K (e (L.annulus.map p)) j) (Metric.ball a rho) := by
  exact L.annulus.exists_local_chart_columns he.continuous hread
    hA.continuousOn ha

theorem M64FreeWeakPhaseAnnulus.raw_seam_extension_energy
    (L : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) :
    (∫ p in O,
      (Q (m64AnnulusSeamExtend L.annulus.map p)
          (m64AnnulusSeamExtend (L.annulus.column 0 : LoopPlane → E) p)
          (m64AnnulusSeamExtend (L.annulus.column 0 : LoopPlane → E) p) +
        Q (m64AnnulusSeamExtend L.annulus.map p)
          (m64AnnulusSeamExtend (L.annulus.column 1 : LoopPlane → E) p)
          (m64AnnulusSeamExtend (L.annulus.column 1 : LoopPlane → E) p)) / 2) =
      2 * L.annulus.energy Q := by
  exact L.annulus.seam_extension_energy Q hQ hei hb

variable [IsManifold (𝓡 n) ∞ M]

theorem M64ObservedWeakAnnulus.weightedEnergy_eq_metric_integral_of_contMDiffOn
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v)
          (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (r : ℝ) (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) :
    A.weightedEnergy Q r =
      ∫ p in S, (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2 := by
  unfold M64ObservedWeakAnnulus.weightedEnergy
  have hcol := A.classical_columns_of_contMDiffOn he hA
  apply integral_congr_ae
  filter_upwards [hcol 0, hcol 1,
    ae_restrict_mem isOpen_interior.measurableSet] with p h0 h1 hp
  have hd : MDifferentiableAt (𝓡 2) (𝓡 n) A.map p :=
    (hA.contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt
      (by simp)
  rw [h0, h1,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he Q hdiag hd 0,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he Q hdiag hd 1]

theorem M64FreeWeakPhaseAnnulus.raw_weightedEnergy_eq_metric_integral
    (L : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v)
          (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (r : ℝ)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.annulus.map S) :
    L.annulus.weightedEnergy Q r =
      ∫ p in S, (r * m60AreaGram g L.annulus.map p 0 0 +
        r⁻¹ * m60AreaGram g L.annulus.map p 1 1) / 2 := by
  exact L.annulus.weightedEnergy_eq_metric_integral_of_contMDiffOn
    g he Q hdiag r hA

end PoincareConjecture
