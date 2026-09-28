import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Cuts.FrontierPL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundarySphere

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}

theorem exists_marked_cut_frontier_sphere (P : OriginalDiskProduct e N j)
    (he : PLDomain e N) (hN : IsCompact N)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (hq : PolyhedralPLInCharts e q (Q ×ˢ Icc l u))
    (hqi : InjOn q (Q ×ˢ Icc l u))
    (himage : q '' (Q ×ˢ Icc l u) = frontier N \ P.openStrip) :
    ∃ H : cubePrismBoundary l u ≃ₜ frontier P.cutCarrier,
      (∀ z, (H z : X) = P.markedCutFrontierMap q l u z) ∧
      (∀ z : D, (H ⟨(z, l), Or.inr ⟨z.property, by simp⟩⟩ : X) =
        P.map (z, (1 / 2 : ℝ))) ∧
      (∀ z : D, (H ⟨(z, u), Or.inr ⟨z.property, by simp⟩⟩ : X) =
        P.map (z, -(1 / 2 : ℝ))) ∧
      (∀ z : Q ×ˢ Icc l u, (H ⟨z, Or.inl z.property⟩ : X) = q z) ∧
      PolyhedralPLInCharts e (P.markedCutFrontierMap q l u) (cubePrismBoundary l u) ∧
      Nonempty (ChartwisePLSphere e (frontier P.cutCarrier)) := by
  have hqN : MapsTo q (Q ×ˢ Icc l u) (frontier N) := by
    intro z hz
    exact (himage.subset ⟨z, hz, rfl⟩).1
  have hfull : P.markedCutFrontierMap q l u '' cubePrismBoundary l u =
      frontier P.cutCarrier := by
    rw [P.markedCutFrontierMap_image q hlu hlower hupper, himage,
      (P.cut_geometry hN hopen).2.2.1]
  let f := P.markedCutFrontierMap q l u
  have hPL := P.polyhedral_markedCutFrontierMap he q hlu hlower hupper hq
  obtain ⟨K, hK, hKS⟩ := exists_finite_cubePrismBoundary hlu
  have hcompact : IsCompact (cubePrismBoundary l u) := by
    rw [← hKS]
    exact K.isCompact_space_of_finite hK
  let : CompactSpace (cubePrismBoundary l u) := isCompact_iff_compactSpace.mp hcompact
  have hc : Continuous (fun z : cubePrismBoundary l u => f z) :=
    continuousOn_iff_continuous_domRestrict.mp hPL.continuousOn
  let H0 : cubePrismBoundary l u ≃ₜ f '' cubePrismBoundary l u :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn f _ (P.markedCutFrontierMap_injOn q hlu
        hlower hupper hqN hqi)) (hc.subtype_mk _)
  let H : cubePrismBoundary l u ≃ₜ frontier P.cutCarrier :=
    H0.trans (Homeomorph.setCongr hfull)
  have hHval (z : cubePrismBoundary l u) : (H z : X) = f z := rfl
  refine ⟨H, hHval, ?_, ?_, ?_, hPL, ?_⟩
  · intro z
    exact P.markedCutFrontierMap_lower q l u z
  · intro z
    exact P.markedCutFrontierMap_upper q hlu z
  · intro z
    exact P.markedCutFrontierMap_lateral q hlu hlower hupper z z.property.1
  · obtain ⟨c, g, hg, hcval⟩ := exists_finitePL_cubePrismBoundary_sphere hlu
    obtain ⟨J, hJ, hJQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
    have hgJ : FinitePiecewiseAffineOn g J.space := hJQ.symm ▸ hg
    have hmap : MapsTo g J.space (cubePrismBoundary l u) := by
      intro z hz
      rw [← hcval ⟨z, hJQ.subset hz⟩]
      exact (c ⟨z, hJQ.subset hz⟩).property
    have hcomp := hPL.comp_finitePiecewiseAffineOn J hJ hgJ hmap
    refine ⟨{
      parametrization := c.trans H
      map := f ∘ g
      map_eq := ?_
      piecewiseAffine := hJQ ▸ hcomp }⟩
    intro z
    change f (g z) = (H (c z) : X)
    rw [← hcval z, hHval]

end PoincareConjecture.M76.OriginalDiskProduct
