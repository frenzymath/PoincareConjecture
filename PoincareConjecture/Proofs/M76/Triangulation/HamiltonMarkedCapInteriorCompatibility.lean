import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedCapCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapInteriorTransition









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonMarkedCapCoordinates

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "M" => (ℝ × V2)

variable {X ι : Type*} [TopologicalSpace X]
  {D S : Set X} {eps : ℝ} {g : S × Ico (0 : ℝ) eps → X}




theorem interior_compatible (c : HamiltonMarkedCapCoordinates (E := V2) (D := D) g)
    {e : ι → OpenPartialHomeomorph X V3} (s : ChartwisePLSphere e S)
    (a q : M ≃ᴬ[ℝ] V3) (C : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans
      (c.original.transHomeomorph a.toHomeomorph) ∈ piecewiseAffineGroupoid V3)
    (hg : ∀ p, g p ∈ D) (hC : C.source = interior D)
    (hcollar : ∀ p, C (g p) =
      unitCubeInwardCollarMap ((s.parametrization.symm p.1 : V3), (p.2 : ℝ))) :
    (c.chart.transHomeomorph q.toHomeomorph).symm.trans C ∈ piecewiseAffineGroupoid V3 := by
  let B := c.original.transHomeomorph a.toHomeomorph
  let H := c.chart.transHomeomorph q.toHomeomorph
  let Z : M →L[ℝ] M :=
    (0 : M →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ V2)
  let z : V3 →ᴬ[ℝ] V3 := a.toContinuousAffineMap.comp
    (Z.toContinuousAffineMap.comp q.symm.toContinuousAffineMap)
  let depth : V3 →ᴬ[ℝ] ℝ :=
    (-(ContinuousLinearMap.fst ℝ ℝ V2).toContinuousAffineMap).comp q.symm.toContinuousAffineMap
  have hzt : MapsTo z (H.symm.trans C).source B.target := by
    intro p hp
    have hpq : q.symm p ∈ c.chart.target := hp.1
    have hz : (q.symm p).2 ∈ c.lateral := (c.target.subset hpq).2
    change a.symm (a (0, (q.symm p).2)) ∈ c.original.target
    rw [a.symm_apply_apply]
    exact c.rectangle ⟨⟨neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩, hz⟩
  have hBinv (p : V3) : B.symm (z p) = c.original.symm (0, (q.symm p).2) := by
    change c.original.symm (a.symm (a (0, (q.symm p).2))) = _
    rw [a.symm_apply_apply]
  have hpoint (p : V3) (hp : p ∈ (H.symm.trans C).source) :
      B.symm (z p) = (c.boundary.symm (q.symm p).2 : X) := by
    rw [hBinv]
    exact (c.boundary_inverse _ (c.lateral_subset_boundary_target
      (c.target.subset hp.1).2)).symm
  have himage : ∀ p ∈ (H.symm.trans C).source, B.symm (z p) ∈ S := by
    intro p hp
    rw [hpoint p hp]
    exact (c.boundary.symm (q.symm p).2).property
  apply s.cap_interior_transition_mem_piecewiseAffineGroupoid B H C hcompat z depth hzt himage
  intro p hp
  have hpq : q.symm p ∈ c.chart.target := hp.1
  have hxD : c.chart.symm (q.symm p) ∈ interior D := hC.subset hp.2
  have hnegative : (q.symm p).1 < 0 := by
    have h := (c.interior_side hg _ (c.chart.map_target hpq)).mp hxD
    rw [c.chart.right_inv hpq] at h
    exact h
  obtain ⟨t, ht, _, hval⟩ := c.inverse_nonpos (q.symm p) hpq hnegative.le
  have hs : (⟨B.symm (z p), himage p hp⟩ : S) = c.boundary.symm (q.symm p).2 :=
    Subtype.ext (hpoint p hp)
  change C (c.chart.symm (q.symm p)) =
    unitCubeInwardCollarMap ((s.parametrization.symm ⟨B.symm (z p), himage p hp⟩ : V3), depth p)
  rw [hval, hcollar, hs]
  apply congrArg unitCubeInwardCollarMap
  apply Prod.ext
  · rfl
  · exact ht

end PoincareConjecture.M76.HamiltonMarkedCapCoordinates
