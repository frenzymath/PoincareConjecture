import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallBoundaryCoordinates

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.ChartwisePLBall

local notation "V3" => (Fin 3 → ℝ)
local notation "Cube" => closedBall (0 : V3) 1

theorem exists_finite_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {B S : Set X}
    (b : ChartwisePLBall e B S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgB : MapsTo g K.space B) :
    ∃ q : E → V3, FinitePiecewiseAffineOn q K.space ∧ MapsTo q K.space Cube ∧
      EqOn (b.map ∘ q) g K.space := by
  classical
  let q : E → V3 := fun x ↦ if hx : x ∈ K.space then
    b.parametrization.symm ⟨g x,hgB hx⟩ else 0
  have hqvalue (x : K.space) : q x =
      (b.parametrization.symm ⟨g x,hgB x.property⟩ : V3) := by
    simp only [q,dif_pos x.property]
  have hqcont : ContinuousOn q K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp
      (b.parametrization.symm.continuous.comp (hg.continuousOn.domRestrict.subtype_mk _))).congr
        (fun x ↦ (hqvalue x).symm)
  have hqmap : MapsTo q K.space Cube := by
    intro x hx
    rw [hqvalue ⟨x,hx⟩]
    exact (b.parametrization.symm ⟨g x,hgB hx⟩).property
  have heq : EqOn (b.map ∘ q) g K.space := by
    intro x hx
    change b.map (q x) = g x
    rw [hqvalue ⟨x,hx⟩,b.map_eq,b.parametrization.apply_symm_apply]
  have hbi : InjOn b.map Cube := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (b.isEmbedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  exact ⟨q,b.piecewiseAffine.finitePiecewiseAffineOn_lift hcompat hbi K hK hqcont hqmap
    (hg.congr heq.symm),hqmap,heq⟩

end PoincareConjecture.M76.ChartwisePLBall
