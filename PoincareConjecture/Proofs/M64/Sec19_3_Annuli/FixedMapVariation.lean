import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CurvatureSupremum
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.GramRank
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.RicciQuadratic
import PoincareConjecture.Proofs.M60.Mathlib.GramDeterminantDerivative
import PoincareConjecture.Proofs.M60.Mathlib.GramTraceBound
import PoincareConjecture.Proofs.M60.Mathlib.ExponentialComparison
import PoincareConjecture.Proofs.M60.Mathlib.DominatedDerivative
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.MetricTransport
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import Mathlib.Analysis.Calculus.MeanValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





noncomputable def m64AnnulusRicciTraceDensity
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  let d := mfderiv (𝓡 2) (𝓡 n) f z
  let e : Fin 2 → TangentSpace (𝓡 n) (f z) :=
    fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G := m60AreaGram g f z
  if Matrix.det G = 0 then 0 else
    (∑ i : Fin 2, ∑ j : Fin 2, (G⁻¹) i j * D.ricci (f z) (e j) (e i)) *
      m60AreaDensity g f z





theorem m64AnnulusRicciTraceDensity_eq_zero
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : LoopPlane → M) (z : LoopPlane)
    (hz : Matrix.det (m60AreaGram g f z) = 0) :
    m64AnnulusRicciTraceDensity D f z = 0 := by
  simp only [m64AnnulusRicciTraceDensity, hz, if_true]





theorem m64AnnulusDensity_variation {J : Set ℝ}
    (F : RicciFlow n M J) (f : LoopPlane → M) (z : LoopPlane)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivWithinAt (fun s => m60AreaDensity (F.metric s) f z)
      (-m64AnnulusRicciTraceDensity (F.connection t) f z) J t := by
  by_cases hdeg : Matrix.det (m60AreaGram (F.metric t) f z) = 0
  · rw [m64AnnulusRicciTraceDensity_eq_zero (F.connection t) f z hdeg, neg_zero]
    have hzero : (fun s => m60AreaDensity (F.metric s) f z) =
        fun _ => (0 : ℝ) := by
      funext s
      exact m60AreaDensity_eq_zero_of_det_eq_zero (F.metric t) (F.metric s) f z hdeg
    rw [hzero]
    exact hasDerivWithinAt_const _ _ _
  · let G := fun s => m60AreaGram (F.metric s) f z
    let e := fun i : Fin 2 =>
      mfderiv (𝓡 2) (𝓡 n) f z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)
    let R : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => (F.connection t).ricci (f z) (e i) (e j)
    have hG : ∀ i j, HasDerivWithinAt (fun s => G s i j)
        (-2 * R i j) J t := by
      intro i j
      exact F.equation t ht (f z) (e i) (e j)
    have hnonneg (s : ℝ) : 0 ≤ Matrix.det (G s) := by
      exact m60AreaGram_det_nonneg (F.metric s) f z
    have hpos : 0 < Matrix.det (G t) :=
      lt_of_le_of_ne (hnonneg t) (Ne.symm hdeg)
    have hd := M60.hasDerivWithinAt_sqrt_det_fin_two hG hpos
    have harea : (fun s => Real.sqrt (Matrix.det (G s))) =
        fun s => m60AreaDensity (F.metric s) f z := by
      funext s
      exact congrArg Real.sqrt (max_eq_right (hnonneg s)).symm
    rw [harea] at hd
    convert hd using 1
    unfold m64AnnulusRicciTraceDensity
    rw [if_neg hdeg]
    unfold m60AreaDensity
    rw [max_eq_right (hnonneg t)]
    simp only [Fin.sum_univ_two]
    dsimp only [G, R, e]
    ring





theorem m64AnnulusRicciTraceDensity_abs_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {C : ℝ} (hC : 0 ≤ C)
    (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ C)
    (f : LoopPlane → M) (z : LoopPlane) :
    |m64AnnulusRicciTraceDensity D f z| ≤
      2 * (n : ℝ) * C * m60AreaDensity g f z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let x := f z
  let d := mfderiv (𝓡 2) (𝓡 n) f z
  let v := fun i : Fin 2 =>
    d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G := m60AreaGram g f z
  have harea : 0 ≤ m60AreaDensity g f z :=
    m60AreaDensity_nonneg g f z
  by_cases hdeg : Matrix.det G = 0
  · rw [show G = m60AreaGram g f z from rfl] at hdeg
    rw [m64AnnulusRicciTraceDensity_eq_zero D f z hdeg, abs_zero]
    positivity
  have hpos : 0 < Matrix.det (Matrix.gram ℝ v) := by
    change 0 < Matrix.det (m60AreaGram g f z)
    exact lt_of_le_of_ne (m60AreaGram_det_nonneg g f z) (Ne.symm hdeg)
  obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear D D.curvatureTensorCalculus x
  have hbound (w : TangentSpace (𝓡 n) x) :
      |B w w| ≤ (n : ℝ) * C * inner ℝ w w := by
    rw [hB]
    have hric := M04.abs_ricci_le_curvatureTensorNorm D x w
    have hnorm : (n : ℝ) * D.curvatureTensorNorm x ≤ (n : ℝ) * C :=
      mul_le_mul_of_nonneg_left (hcurv x) (Nat.cast_nonneg n)
    exact hric.trans <| by
      have hinner : 0 ≤ inner ℝ w w := real_inner_self_nonneg
      exact mul_le_mul_of_nonneg_right hnorm hinner
  have htrace :
      |∑ i : Fin 2, ∑ j : Fin 2,
        (m60AreaGram g f z)⁻¹ i j * D.ricci x (v j) (v i)| ≤
        2 * ((n : ℝ) * C) := by
    have h := M60.abs_inverse_gram_contraction_le v B hbound hpos
    change |∑ i : Fin 2, ∑ j : Fin 2,
      (m60AreaGram g f z)⁻¹ i j * B (v j) (v i)| ≤
      2 * ((n : ℝ) * C) at h
    simp_rw [hB] at h
    exact h
  unfold m64AnnulusRicciTraceDensity
  rw [if_neg hdeg, abs_mul, abs_of_nonneg harea]
  exact (mul_le_mul_of_nonneg_right htrace harea).trans_eq (by ring)





theorem m64AnnulusRicciTraceIntegral_abs_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {C : ℝ} (hC : 0 ≤ C)
    (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ C)
    (f : LoopPlane → M)
    (harea : IntegrableOn (m60AreaDensity g f) m64AnnulusDomain volume)
    (htrace : IntegrableOn (m64AnnulusRicciTraceDensity D f)
      m64AnnulusDomain volume) :
    |-(∫ z in m64AnnulusDomain, m64AnnulusRicciTraceDensity D f z)| ≤
      2 * (n : ℝ) * C * m64AnnulusArea g f := by
  rw [abs_neg]
  calc
    _ ≤ ∫ z in m64AnnulusDomain, ‖m64AnnulusRicciTraceDensity D f z‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (m64AnnulusRicciTraceDensity D f) (μ := volume.restrict m64AnnulusDomain)
    _ ≤ ∫ z in m64AnnulusDomain, 2 * (n : ℝ) * C * m60AreaDensity g f z :=
      integral_mono htrace.norm (harea.const_mul _) (fun z => by
        simpa only [Real.norm_eq_abs] using
          m64AnnulusRicciTraceDensity_abs_le D hC hcurv f z)
    _ = _ := integral_const_mul _ _






theorem m64AnnulusArea_variation_of_curvature_bound
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b))
    {C : ℝ} (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ C)
    (f : LoopPlane → M)
    (harea : ∀ s : ℝ,
      IntegrableOn (m60AreaDensity (F.metric s) f) m64AnnulusDomain volume) :
    ∀ t ∈ Icc a b,
      IntegrableOn (m64AnnulusRicciTraceDensity (F.connection t) f)
        m64AnnulusDomain volume ∧
      HasDerivWithinAt (fun s => m64AnnulusArea (F.metric s) f)
        (-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (F.connection t) f z)) (Icc a b) t ∧
      |-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (F.connection t) f z)| ≤
        2 * (n : ℝ) * C * m64AnnulusArea (F.metric t) f := by
  let A := fun s z => m60AreaDensity (F.metric s) f z
  let V := fun s z => -m64AnnulusRicciTraceDensity (F.connection s) f z
  let D : ℝ := 2 * (n : ℝ) * C
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hd (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => A s z) (V t z) (Icc a b) t :=
    m64AnnulusDensity_variation F f z ht
  have hv (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) :
      |V t z| ≤ D * A t z := by
    simpa only [A, V, D, abs_neg] using
      m64AnnulusRicciTraceDensity_abs_le (F.connection t) hC (hcurv t ht) f z
  let K := Real.exp (D * (b - a))
  have hA (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) : A t z ≤ K * A a z := by
    have h := M60.le_exp_abs_mul_of_abs_deriv_le (hd z) (hv z)
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hD))
      (m60AreaDensity_nonneg (F.metric a) f z))
  let bound := fun z => D * K * A a z
  have hbound : Integrable bound (volume.restrict m64AnnulusDomain) :=
    (harea a).const_mul (D * K)
  have hV (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) : ‖V t z‖ ≤ bound z := by
    rw [Real.norm_eq_abs]
    exact (hv z t ht).trans (by
      simpa only [bound, mul_assoc] using
        mul_le_mul_of_nonneg_left (hA z t ht) hD)
  have hlip (z : LoopPlane) {t s : ℝ} (ht : t ∈ Icc a b) (hs : s ∈ Icc a b) :
      ‖A s z - A t z‖ ≤ bound z * ‖s - t‖ :=
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => A s z) (f' := fun s => V s z) (hd z) (hV z) ht hs
  intro t ht
  let : NeBot (𝓝[Icc a b \ {t}] t) :=
    accPt_principal_iff_nhdsWithin.mp ((uniqueDiffOn_Icc hab) t ht).accPt
  have hintegral := M60.hasDerivWithinAt_integral_of_dominated_lipschitz
    (mu := volume.restrict m64AnnulusDomain) harea hbound
    (Eventually.of_forall fun z s hs => hlip z ht hs)
    (Eventually.of_forall fun z => hd z t ht)
  have htrace : IntegrableOn (m64AnnulusRicciTraceDensity (F.connection t) f)
      m64AnnulusDomain volume := integrable_neg_iff.mp hintegral.1
  refine ⟨htrace, ?_, m64AnnulusRicciTraceIntegral_abs_le
    (F.connection t) hC (hcurv t ht) f (harea t) htrace⟩
  simpa only [A, V, m64AnnulusArea, integral_neg] using hintegral.2





theorem m64AnnulusArea_variation_on_compact
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    ∀ t ∈ Icc a b,
      IntegrableOn (m64AnnulusRicciTraceDensity (F.connection t) f)
        m64AnnulusDomain volume ∧
      HasDerivWithinAt (fun s => m64AnnulusArea (F.metric s) f)
        (-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (F.connection t) f z)) (Icc a b) t ∧
      |-(∫ z in m64AnnulusDomain,
          m64AnnulusRicciTraceDensity (F.connection t) f z)| ≤
        2 * (n : ℝ) * m64CurvatureSupremum F t * m64AnnulusArea (F.metric t) f := by
  obtain ⟨C, hC, hcurv⟩ := m64_compact_flow_curvature_bound F hcompact
  have harea (s : ℝ) :
      IntegrableOn (m60AreaDensity (F.metric s) f) m64AnnulusDomain volume :=
    (m60AreaDensity_continuous (F.metric s) hf).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact
  intro t ht
  obtain ⟨htrace, hderiv, _⟩ :=
    m64AnnulusArea_variation_of_curvature_bound hab F hC hcurv f harea t ht
  have hbounded := m64CurvatureRange_bddAbove_of_compact (F := F) hcompact ht
  exact ⟨htrace, hderiv, m64AnnulusRicciTraceIntegral_abs_le (F.connection t)
    (m64CurvatureSupremum_nonneg hbounded) (m64Curvature_le_supremum hbounded)
    f (harea t) htrace⟩

end PoincareConjecture
