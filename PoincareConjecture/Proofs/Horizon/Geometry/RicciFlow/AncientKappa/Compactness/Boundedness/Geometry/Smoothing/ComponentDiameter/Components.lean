import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Collars
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientCompactness

private theorem locallyConnectedSpace_regular_level
    {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateThree M]
    [IsManifold (𝓡 3) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {O : Set M} (hO : IsOpen O)
    (hreg : ∀ x ∈ O, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0) (a : ℝ) :
    LocallyConnectedSpace {x | x ∈ O ∧ f x = a} := by
  let U : TopologicalSpace.Opens M := ⟨O, hO⟩
  let S := {x | x ∈ O ∧ f x = a}
  let : Fact (Module.finrank ℝ CoordinateThree = 2 + 1) :=
    ⟨by simp [CoordinateThree]⟩
  let := Poincare.Geometry.Manifold.RegularLevel.openLevelSetChartedSpace hf U hreg 2 a
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2))
    (Poincare.Geometry.Manifold.RegularLevel.openLevelSet f U a)
  let e : S ≃ₜ Poincare.Geometry.Manifold.RegularLevel.openLevelSet f U a :=
    { toFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact e.locallyConnectedSpace

theorem exists_uniform_regular_level_component_diameter
    {M : Type*} [MetricSpace M] [ChartedSpace CoordinateThree M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {K O : Set M} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ d : ℝ, 0 < d ∧ ∀ (f : M → ℝ), ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f →
      (∀ x ∈ O, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0) →
      ∀ a : ℝ, IsCompact {x | x ∈ O ∧ f x = a} →
        {x | x ∈ O ∧ f x = a} ⊆ K →
      ∀ x ∈ {x | x ∈ O ∧ f x = a},
        ∃ y ∈ connectedComponentIn {x | x ∈ O ∧ f x = a} x,
        ∃ z ∈ connectedComponentIn {x | x ∈ O ∧ f x = a} x,
          d ≤ dist y z := by
  obtain ⟨d, hd, hbound⟩ := exists_uniform_collared_regular_level_diameter hK hO hKO
  refine ⟨d, hd, ?_⟩
  intro f hf hreg a hS hSK x hx
  let S := {y | y ∈ O ∧ f y = a}
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : LocallyConnectedSpace S := locallyConnectedSpace_regular_level hf hO hreg a
  let p : S := ⟨x, hx⟩
  let C := connectedComponent p
  have hC : IsOpen C := isOpen_connectedComponent
  let : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨s, hs, U, hU, _, e, he⟩ := D.exists_collar_of_compact_regular_level hf hO hreg a hS
  let j : (C × Ioo (-s) s) → (S × Ioo (-s) s) := Prod.map Subtype.val id
  have hj : IsOpenEmbedding j := hC.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  let F : (C × Ioo (-s) s) → M := fun z => (e (j z) : M)
  have hF : IsOpenEmbedding F := hU.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hj)
  let c := hF.isEmbedding.toHomeomorph
  have hcenter (y : C) : (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) = y.1.1 := by
    exact he y.1
  obtain ⟨y, z, hyz⟩ := hbound f (hf.mdifferentiable (by simp)).mdifferentiableOn hreg
    C (range F) hF.isOpen_range s hs c
    (fun y => by rw [hcenter]; exact hSK y.1.property) a
    (fun y => by rw [hcenter]; exact y.1.property.2)
  rw [hcenter, hcenter] at hyz
  rw [connectedComponentIn_eq_image hx]
  exact ⟨y.1.1, ⟨y.1, y.2, rfl⟩, z.1.1, ⟨z.1, z.2, rfl⟩, hyz⟩

end PoincareConjecture.AncientCompactness
