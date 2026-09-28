import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.FiniteComponents
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalIntegral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators
open Poincare.Geometry.Manifold.RegularLevel

theorem PoincareConjecture.LeviCivitaData.integral_regularLevel_pos_scalar_le_of_component_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric (n+1) M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ f)
    (t : ℝ) (hcompact : IsCompact (f ⁻¹' {t}))
    (hreg : ∀ x, f x=t → mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f x≠0)
    {K : M → ℝ} (hK : ContinuousOn K (g.regularDomain hf)) (β : ℝ)
    {A C : ℝ} (hA : 0≤A) (hC : 0≤C) (N : ℕ) :
    let U := g.regularDomain hf
    let hr := g.regularDomain_regular hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hr n t
    letI := isManifold_openLevelSet hf U hr n t
    let L := openLevelSet f U t
    let gL := g.regularLevelMetric hf U hr t
    let E := fun x:L => D.levelSectionalError f K β (openLevelIncl f U t x)
    Nat.card (ConnectedComponents L)≤N →
    (∀ p:L,
      (∫ x, max 0 ((gL.connectedComponentMetric p).leviCivitaData.scalarCurvature x)
        ∂(gL.connectedComponentMetric p).volumeMeasure) ≤
      C*(A+∫ x, E x ∂(gL.connectedComponentMetric p).volumeMeasure)) →
    (∫ x, max 0 (gL.leviCivitaData.scalarCurvature x) ∂g.regularLevelVolume hf U hr t) ≤
      C*((N:ℝ)*A+∫ x, E x ∂g.regularLevelVolume hf U hr t) := by
  let U := g.regularDomain hf
  let hr := g.regularDomain_regular hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hr n t
  let := isManifold_openLevelSet hf U hr n t
  let L := openLevelSet f U t
  let gL := g.regularLevelMetric hf U hr t
  let incl := openLevelIncl f U t
  let E := fun x:L => D.levelSectionalError f K β (incl x)
  have hsub : f ⁻¹' {t}⊆(U:Set M) :=
    fun x hx => (g.mem_regularDomain_iff hf x).mpr (hreg x hx)
  have hLc : IsCompact (univ:Set L) := by
    apply (isEmbedding_openLevelIncl f U t).isCompact_iff.mpr
    rw [image_univ,range_openLevelIncl,inter_eq_right.mpr hsub]
    exact hcompact
  let : CompactSpace L := isCompact_univ_iff.mp hLc
  have hEc : Continuous E :=
    (D.continuousOn_levelSectionalError_regularDomain hf hK β).comp_continuous
      (contMDiff_openLevelIncl hf U hr n t).continuous (fun x => x.1.2)
  have hEi : Integrable E gL.volumeMeasure :=
    hEc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace E)
  dsimp only
  intro hcount hbound
  exact gL.integral_pos_scalarCurvature_le_of_connectedComponent_bounds gL.leviCivitaData
    E hEi hA hC N hcount hbound
