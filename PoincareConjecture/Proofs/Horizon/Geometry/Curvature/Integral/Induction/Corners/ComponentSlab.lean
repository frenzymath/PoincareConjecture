import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleAnnulusBound
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ComponentAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology
universe u
theorem PoincareConjecture.LeviCivitaData.integral_scalarCurvature_posPart_inner_slab_le_of_component_induction
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    {g : RiemannianMetric (m + 2) M} (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b α C A : ℝ} (ha : 0 < a) (hab : a < b)
    (hm : 2 ≤ m + 1) (hα : 0 < α) (hC : 0 ≤ C) (hA : 0 ≤ A) (N : ℕ)
    (hslab : Icc a (3 * b / 2) ⊆ I)
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
    let Q := α * C + ((m + 2 : ℕ) : ℝ) ^ 2
    let P := α * C * (((m + 1 : ℕ) : ℝ) * (1 + α) * α ^ 3 + α ^ 2) +
      ((m + 1 : ℕ) : ℝ) * (α ^ 2 + α ^ 3)
    (∀ t ∈ Icc a (3 * b / 2),
      Nat.card (ConnectedComponents (openLevelSet f U t)) ≤ N) →
    (∀ t ∈ Icc a (3 * b / 2), ∀ p : openLevelSet f U t,
      let gL := RiemannianMetric.regularLevelMetric
        hf U (g.regularDomain_regular hf) t g
      (∫ z, max 0 ((gL.connectedComponentMetric p).leviCivitaData.scalarCurvature z)
        ∂(gL.connectedComponentMetric p).volumeMeasure) ≤
      C * (A + ∫ z, D.levelSectionalError f K (α / t)
        (openLevelIncl f U t z) ∂(gL.connectedComponentMetric p).volumeMeasure)) →
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * Q * (∫ x in f ⁻¹' Icc a (3 * b / 2), K x ∂g.volumeMeasure) +
      3 * α * C * ((N : ℝ) * A) * b + 2 * P * (3 * b / 2) ^ m + 4 * α * b ^ m := by
  classical
  dsimp only
  intro hcount hind
  apply D.integral_scalarCurvature_posPart_inner_slab_le_of_scaled_level_induction
    hf hI hproper hreg ha hab hm hα hC (mul_nonneg (Nat.cast_nonneg N) hA)
    hslab hKc hK hsec harea hhess hspeed
  intro t ht
  have hti : t ∈ I := hslab ht
  have hcompact : IsCompact (f ⁻¹' {t}) := by
    simpa only [Icc_self] using Poincare.Coarea.isCompact_slab_of_isProperMap hproper
      (show Icc t t ⊆ I by simpa only [Icc_self, singleton_subset_iff] using hti)
  exact D.integral_regularLevel_pos_scalar_le_of_component_bounds hf t hcompact
    (fun x hx => hreg x (by rwa [hx])) hKc (α / t) hA hC N (hcount t ht) (hind t ht)
