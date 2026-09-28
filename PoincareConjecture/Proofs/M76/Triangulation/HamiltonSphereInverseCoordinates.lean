import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInverseChart

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι G : Type*} [TopologicalSpace X]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem ChartwisePLSphere.exists_locallyPL_inverse_chart_parameterization
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (c : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans c ∈ piecewiseAffineGroupoid V3)
    {g : G → V3} {U : Set G} (hg : LocallyPiecewiseAffineOn g U)
    (hgt : MapsTo g U c.target) (himage : ∀ y ∈ U, c.symm (g y) ∈ S) :
    ∃ q : G → V3, LocallyPiecewiseAffineOn q U ∧
      ∀ y (hy : y ∈ U), q y =
        (s.parametrization.symm ⟨c.symm (g y), himage y hy⟩ : V3) := by
  classical
  let q : G → V3 := fun y => if hy : y ∈ U then
    (s.parametrization.symm ⟨c.symm (g y), himage y hy⟩ : V3) else 0
  have hqval (y : G) (hy : y ∈ U) : q y =
      (s.parametrization.symm ⟨c.symm (g y), himage y hy⟩ : V3) := by
    simp only [q, dif_pos hy]
  have hq : ContinuousOn q U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun y : U => c.symm (g y)) :=
      c.continuousOn_invFun.comp_continuous hg.continuousOn.domRestrict
        (fun y => hgt y.property)
    have hs : Continuous (fun y : U =>
        (⟨c.symm (g y), himage y y.property⟩ : S)) := hc.subtype_mk _
    exact (continuous_subtype_val.comp (s.parametrization.symm.continuous.comp hs)).congr
      (fun y => (hqval y y.property).symm)
  have hinj : InjOn s.map (Metric.sphere (0 : V3) 1) := by
    intro y hy z hz h
    have heq : s.parametrization ⟨y, hy⟩ = s.parametrization ⟨z, hz⟩ :=
      Subtype.ext ((s.map_eq ⟨y, hy⟩).symm.trans (h.trans (s.map_eq ⟨z, hz⟩)))
    exact congrArg Subtype.val (s.parametrization.injective heq)
  refine ⟨q, s.piecewiseAffine.locallyPiecewiseAffineOn_inverse_comp hinj c ?_
    hg hq ?_ hgt ?_, hqval⟩
  · intro i
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hcompat i)
  · intro y hy
    rw [hqval y hy]
    exact (s.parametrization.symm ⟨c.symm (g y), himage y hy⟩).property
  · intro y hy
    rw [hqval y hy]
    exact (s.map_eq (s.parametrization.symm ⟨c.symm (g y), himage y hy⟩)).trans
      (congrArg Subtype.val (s.parametrization.apply_symm_apply _))

end PoincareConjecture.M76
