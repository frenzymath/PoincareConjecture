import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralChartCapInduction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralOpenCapUnion
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactSupportOneZero
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralManifoldOrientation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralManifoldSupport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.ThreeManifoldTriangulation










set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set
open scoped Manifold ContDiff Topology

universe u

namespace Poincare.Topology


theorem integralThreeManifoldHomologyTwo_isZero_typeZero
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) X]
    [SimplyConnectedSpace X] :
    IsZero (integralHomology X 2) := by
  classical
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) X
  let x0 : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨omegaX, hgenX, hlocalX⟩ :=
    exists_integralThreeLocallyRepresentedGenerators x0
  let hDX : ∀ K : Set X, IsCompact K → IntegralSupportDetected K 3 :=
    fun K hK => (integralThreeManifoldCompactSupport K hK).2
  let U : X → Set X := fun x => (chartAt (EuclideanSpace Real (Fin 3)) x).source
  have hU (x : X) : IsOpen (U x) :=
    (chartAt (EuclideanSpace Real (Fin 3)) x).open_source
  have hchart (x : X) (W : Set X) (hW : IsOpen W) (hWx : W ⊆ U x) :
      integralOpenCapProperty hDX omegaX hlocalX W hW :=
    integralOpenCapProperty_of_chart hDX omegaX hlocalX hgenX
      (chartAt (EuclideanSpace Real (Fin 3)) x) W hW hWx

  have hfinite (s : Finset X) :
      ∀ (W : Set X) (hW : IsOpen W), W ⊆ ⋃ x ∈ s, U x →
        integralOpenCapProperty hDX omegaX hlocalX W hW := by
    induction s using Finset.induction_on with
    | empty =>
        intro W hW hWs
        apply hchart x0 W hW
        intro x hx
        have h := hWs hx
        simp at h
    | @insert x s hx ih =>
        intro W hW hWs
        let S : Set X := ⋃ y ∈ s, U y
        have hS : IsOpen S := isOpen_biUnion fun y _ => hU y
        have hleft := hchart x (W ∩ U x) (hW.inter (hU x)) inter_subset_right
        have hright := ih (W ∩ S) (hW.inter hS) inter_subset_right
        have hinter := hchart x ((W ∩ U x) ∩ (W ∩ S))
          ((hW.inter (hU x)).inter (hW.inter hS))
          (fun _ hz => hz.1.2)
        have hprop := integralOpenCapProperty_union hDX omegaX hlocalX
          (W ∩ U x) (W ∩ S) (hW.inter (hU x)) (hW.inter hS)
          hleft hright hinter
        have hset : (W ∩ U x) ∪ (W ∩ S) = W := by
          apply subset_antisymm
          · rintro y (hy | hy)
            · exact hy.1
            · exact hy.1
          · intro y hy
            have hmem : y ∈ U x ∪ S := by
              simpa only [Finset.set_biUnion_insert] using hWs hy
            rcases hmem with hmem | hmem
            · exact Or.inl ⟨hy, hmem⟩
            · exact Or.inr ⟨hy, hmem⟩
        simpa only [hset] using hprop
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace Real (Fin 3)) x⟩)
  have hwhole := hfinite s univ isOpen_univ hs
  let e := Homeomorph.Set.univ X
  let : CompactSpace (univ : Set X) := e.symm.compactSpace
  let : SimplyConnectedSpace (univ : Set X) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyCompactSpace (univ : Set X) := isOpen_univ.locallyCompactSpace
  let d1 := integralCompactSupportCapOne
    (integralOpenSupportDetectedData univ hDX isOpen_univ)
    (integralOpenOmegaData isOpen_univ omegaX)
    (integralOpenLocalOrientationData isOpen_univ omegaX hlocalX)
  let : Epi d1 := hwhole.1
  have hzero : IsZero (integralHomology (univ : Set X) 2) :=
    IsZero.of_epi d1 (integralCompactSupportCohomology_one_isZero (univ : Set X))
  have hsub : Subsingleton (integralHomology (univ : Set X) 2) :=
    ModuleCat.subsingleton_of_isZero hzero
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨?_⟩
  intro a b
  apply (integralHomeomorphHomologyEquiv e 2).symm.injective
  exact @Subsingleton.elim _ hsub _ _

theorem integralThreeManifoldHomologyTwo_isZero
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [SimplyConnectedSpace M] :
    IsZero (integralHomology M 2) := by
  obtain ⟨I, horder, hfinite, ⟨e⟩, _⟩ :=
    exists_compact_three_manifold_finite_triangulation (M := M)
  let := horder
  let := hfinite
  let X := (finiteOrderComplex I).space
  let : T2Space X := e.isEmbedding.t2Space
  let : CompactSpace X := e.symm.compactSpace
  let : ChartedSpace (EuclideanSpace Real (Fin 3)) X := e.symm.chartedSpace
  let : SimplyConnectedSpace X := e.toHomotopyEquiv.simplyConnectedSpace
  have hzero := integralThreeManifoldHomologyTwo_isZero_typeZero (X := X)
  have hsub : Subsingleton (integralHomology X 2) :=
    ModuleCat.subsingleton_of_isZero hzero
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨?_⟩
  intro a b
  apply (integralHomeomorphHomologyEquiv e 2).symm.injective
  exact @Subsingleton.elim _ hsub _ _

end Poincare.Topology
