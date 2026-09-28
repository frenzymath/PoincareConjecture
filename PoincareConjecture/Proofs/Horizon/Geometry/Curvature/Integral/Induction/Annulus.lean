import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Intermediate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.AreaEstimates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [IsManifold (𝓡 (m + 2)) ∞ M]
  {g : RiemannianMetric (m + 2) M}



theorem integral_scalarCurvature_posPart_inner_slab_le_of_level_induction
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α C : ℝ} (ha : 0 < a) (hab : a < b) (hb : 3 * b / 2 ≤ 1)
    (hm : 2 ≤ m + 1) (hα : 0 < α) (hC : 0 ≤ C) (hslab : Icc a (3 * b / 2) ⊆ I)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x ∈ f ⁻¹' Icc a (3 * b / 2), 0 ≤ K x)
    (hsec : ∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
      ∀ v w : TangentSpace (𝓡 (m + 2)) x, -K x ≤ D.sectionalCurvature x v w)
    (harea : ∀ t ∈ Icc a (3 * b / 2),
      g.regularLevelArea hf t ≤ α * t ^ (m + 1))
    (hhess : ∀ t ∈ Icc a (3 * b / 2), ∀ x, f x = t →
      ∀ v : TangentSpace (𝓡 (m + 2)) x,
        g.inner x (D.gradient f x) v = 0 →
        D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ (α / t) * g.inner x v v)
    (hspeed : ∀ x ∈ f ⁻¹' Icc a (3 * b / 2),
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
    letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
    let DL := fun t => (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) t g).leviCivitaData
    let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
    let L := α * C * (1 + ((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
      ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
    (∀ t ∈ Icc a (3 * b / 2),
      (∫ z, max 0 ((DL t).scalarCurvature z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
      C * (1 + ∫ z, D.levelSectionalError f K (α / t) (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)) →
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * (max Q L + 2 * α) *
        (1 + ∫ x in f ⁻¹' Icc a (3 * b / 2), K x ∂g.volumeMeasure) := by
  let U := g.regularDomain hf
  let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
  let L := α * C * (1 + ((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
    ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
  let R := ∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure
  let J := ∫ x in f ⁻¹' Icc a (3 * b / 2), K x ∂g.volumeMeasure
  dsimp only
  intro hind
  have hbpos : 0 < b := ha.trans hab
  have hbb : b ≤ 3 * b / 2 := by linarith only [hbpos]
  have hb1 : b ≤ 1 := hbb.trans hb
  have hc := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  have hU : f ⁻¹' Icc a (3 * b / 2) ⊆ U := fun x hx =>
    (g.mem_regularDomain_iff hf x).mpr (hreg x (hslab hx))
  have hiK := (hKc.mono hU).integrableOn_compact hc (μ := g.volumeMeasure)
  have hiR := ((continuous_const (y := (0 : ℝ))).max D.continuous_scalarCurvature).continuousOn.integrableOn_compact
    hc (μ := g.volumeMeasure)
  have hJ : 0 ≤ J :=
    setIntegral_nonneg ((isClosed_Icc.preimage hf.continuous).measurableSet) hK
  have hQ : 0 ≤ Q := add_nonneg (mul_nonneg hα.le hC) (sq_nonneg _)
  have houter : Icc b (3 * b / 2) ⊆ I := by
    intro t ht
    exact hslab ⟨hab.le.trans ht.1, ht.2⟩
  have hhalf : R / 2 ≤ (max Q L + 2 * α) * (1 + J) := by
    apply D.regularLevelArea_le_mul_one_add_of_forall_le_sub_meanCurvature
      hf hI hproper hreg hbpos hb1 (by omega : 1 ≤ m + 1) hα.le hJ houter
      (harea b ⟨hab.le, hbb⟩)
    intro t ht
    have hsub : Icc a t ⊆ Icc a (3 * b / 2) :=
      fun _ hx => ⟨hx.1, hx.2.trans ht.2.le⟩
    have hsubM : f ⁻¹' Icc a t ⊆ f ⁻¹' Icc a (3 * b / 2) :=
      preimage_mono hsub
    have hat : a < t := hab.trans ht.1
    have hinter := D.integral_scalarCurvature_posPart_slab_le_of_level_induction
      hf hI hproper hreg ha hat (ht.2.le.trans hb) hm hα hC (hsub.trans hslab) hKc
      (fun x hx => hK x (hsubM hx)) (fun x hx => hsec x (hsubM hx))
      (fun s hs => harea s (hsub hs)) (fun s hs => hhess s (hsub hs))
      (fun x hx => hspeed x (hsubM hx)) (fun s hs => hind s (hsub hs))
    have hmonoR : R ≤ ∫ x in f ⁻¹' Icc a t, max 0 (D.scalarCurvature x) ∂g.volumeMeasure :=
      setIntegral_mono_set (hiR.mono_set hsubM)
        (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
        (Filter.Eventually.of_forall (fun _ hx => ⟨hx.1, hx.2.trans ht.1.le⟩))
    have hKae : 0 ≤ᵐ[g.volumeMeasure.restrict (f ⁻¹' Icc a (3 * b / 2))] K := by
      filter_upwards [ae_restrict_mem ((isClosed_Icc.preimage hf.continuous).measurableSet)] with x hx
      exact hK x hx
    have hmonoK : (∫ x in f ⁻¹' Icc a t, K x ∂g.volumeMeasure) ≤ J :=
      setIntegral_mono_set hiK hKae (Filter.Eventually.of_forall hsubM)
    have hscaledK := mul_le_mul_of_nonneg_left hmonoK
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hQ)
    have hquot : R / 2 ≤ Q * J + L - deriv (g.regularLevelArea hf) t := by
      dsimp only [Q, L] at hscaledK ⊢
      nlinarith only [hinter, hmonoR, hscaledK]
    have hconstant : Q * J + L ≤ max Q L * (1 + J) := by
      have hleft := mul_le_mul_of_nonneg_right (le_max_left Q L) hJ
      have hright := le_max_right Q L
      nlinarith only [hleft, hright]
    have hderiv := (D.first_variation_regularLevelArea hf hI hproper hreg).2
      t (houter (Ioo_subset_Icc_self ht))
    rw [← hderiv.deriv]
    exact hquot.trans (sub_le_sub_right hconstant _)
  change R ≤ 2 * (max Q L + 2 * α) * (1 + J)
  nlinarith only [hhalf]

end PoincareConjecture.LeviCivitaData
