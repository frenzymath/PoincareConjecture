import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Slab
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Coarea
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology



theorem PoincareConjecture.LeviCivitaData.integral_scalarCurvature_posPart_le_regularLevels
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric (m + 2) M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hc : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x ∈ f ⁻¹' Icc a b,
      mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {K : M → ℝ} (hKc : ContinuousOn K (f ⁻¹' Icc a b))
    (hK : ∀ x ∈ f ⁻¹' Icc a b, 0 ≤ K x)
    (hsec : ∀ x ∈ f ⁻¹' Icc a b, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -K x ≤ D.sectionalCurvature x v w) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI (c : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) c
    letI (c : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) c
    let DL := fun c => (PoincareConjecture.RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) c g).leviCivitaData
    (∫ x in f ⁻¹' Icc a b, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      2 * (∫ c in Icc a b, ∫ z,
        max 0 ((DL c).scalarCurvature z) /
          g.tangentNorm (openLevelIncl f U c z)
            (g.gradient f (openLevelIncl f U c z))
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) c) +
      2 * ((m + 2 : ℕ) : ℝ) ^ 2 * (∫ x in f ⁻¹' Icc a b, K x ∂g.volumeMeasure) +
      2 * (∫ z, D.levelMeanCurvature f (openLevelIncl f U a z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) a) -
      2 * (∫ z, D.levelMeanCurvature f (openLevelIncl f U b z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) b) := by
  let U := g.regularDomain hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  let (c : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) c
  let (c : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) c
  let DL := fun c => (PoincareConjecture.RiemannianMetric.regularLevelMetric
    hf U (g.regularDomain_regular hf) c g).leviCivitaData
  let L := fun x => D.scalarCurvature x -
    2 * D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x) +
    D.levelGaussTerm f x
  have hUq : (U : Set M) ⊆ {x | 0 < D.levelQ f x} := by
    intro x hx
    change 0 < Real.sqrt (D.levelQ f x) at hx
    exact Real.sqrt_pos.mp hx
  have hKU : f ⁻¹' Icc a b ⊆ U :=
    fun x hx => (g.mem_regularDomain_iff hf x).mpr (hreg x hx)
  have hLc : ContinuousOn L U :=
    (D.continuous_scalarCurvature.continuousOn.sub
      ((D.continuousOn_ricci_levelUnitNormal hf).mono hUq |>.const_mul 2)).add
      ((D.continuousOn_levelGaussTerm hf).mono hUq)
  have hLpos : ContinuousOn (fun x => max 0 (L x)) U :=
    fun x hx => continuousWithinAt_const.max (hLc x hx)
  have heq := g.integral_coarea_compact_slab hf U (g.regularDomain_regular hf) hc hKU hLpos
  have hlevel (c : ℝ) (z : openLevelSet f U c) :
      (DL c).scalarCurvature z = L (openLevelIncl f U c z) :=
    D.regularLevel_scalarCurvature_gauss g hf U (g.regularDomain_regular hf) c (DL c) z
  have hinner (c : ℝ) :
      (∫ z, max 0 (L (openLevelIncl f U c z)) /
          g.tangentNorm (openLevelIncl f U c z) (g.gradient f (openLevelIncl f U c z))
          ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) c) =
        ∫ z, max 0 ((DL c).scalarCurvature z) /
          g.tangentNorm (openLevelIncl f U c z) (g.gradient f (openLevelIncl f U c z))
          ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) c := by
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hlevel]
  simp_rw [hinner] at heq
  have hbound := D.integral_scalarCurvature_posPart_slab_le hf hab hc hreg hKc hK hsec
  dsimp only at hbound
  dsimp only [L] at heq
  rw [heq] at hbound
  exact hbound
