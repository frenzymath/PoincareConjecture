import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.MaximalOriginalSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedComponentPortBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalExteriorNonspherical
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.InteriorChartBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

universe u v
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_maximal_exterior_sphere_cut
    {ι : Type u} {κ : Type v} {α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D) :
    let R := closure (latticeHandleDomain ι κ L \ D)
    ∃ (t : Finset R) (f : LatticeHandleAmbient ι κ L → (t → ℝ × V3))
      (K : SimplicialComplex ℝ (t → ℝ × V3)) (H : R ≃ₜ K.space)
      (g : (t → ℝ × V3) → R),
      (∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target) ∧ InjOn f R ∧
      K.faces.Finite ∧ (∀ x : R, (H x : t → ℝ × V3) = f x) ∧
      (∀ z : K.space, (g z : LatticeHandleAmbient ι κ L) = H.symm z) ∧
      PolyhedralPLInCharts e (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space ∧
      ∃ (ν : Type (max u v)) (_ : Fintype ν) (c : MarkedSphereCut e R ν),
        HasNoPuncturedSphereComponents e f c.carrier ∧
        (∀ (μ : Type (max u v)) [Fintype μ] (d : MarkedSphereCut e R μ),
          HasNoPuncturedSphereComponents e f d.carrier → Fintype.card μ ≤ Fintype.card ν) ∧
        ∀ (T : Set (LatticeHandleAmbient ι κ L)), ChartwisePLSphere e T →
          T ⊆ interior c.carrier →
          ∃ (d : MarkedSphereCut e R (Option ν)) (x : LatticeHandleAmbient ι κ L),
            d.spheres = (fun j : Option ν => j.elim T c.spheres) ∧
            (∀ j, d.collar (some j) = c.collar j) ∧
            (∀ j b, d.ports (some j,b) = c.ports (j,b)) ∧
            d.carrier = c.carrier \ d.collar none ∧
            closure (d.collar none) ⊆ interior c.carrier ∧ x ∈ d.carrier ∧
            HasPuncturedSphereModel e f (connectedComponentIn d.carrier x) ∧
            Disjoint (connectedComponentIn d.carrier x) (frontier R) ∧
            frontier (connectedComponentIn d.carrier x) =
              (⋃ j : {j : Option ν × Bool // d.ports j ⊆ connectedComponentIn d.carrier x}, d.ports j) ∧
            ∃ b : Bool, d.ports (none,b) ⊆ connectedComponentIn d.carrier x := by
  classical
  let R := closure (latticeHandleDomain ι κ L \ D)
  obtain ⟨hR,hsub,_,_,_,hreg,_⟩ := bD.closed_complement_geometry he hdim hi
  have heR := bD.plDomain_closed_complement he hdim hi
  have hRc := bD.isConnected_closed_complement he hdim hi
  have hne : (interior R).Nonempty := by
    by_contra hn
    have hh : interior R = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hreg' : closure (interior R) = R := hreg
    have hh' : R = ∅ := by rw [← hreg',hh,closure_empty]
    exact hRc.nonempty.ne_empty hh'
  obtain ⟨B,hB,⟨bB⟩⟩ := heR.exists_interior_chart_ball hne
  obtain ⟨t,f,K,H,g,hf,hfi,hK,hH,hg,hgPL,hm⟩ :=
    exists_maximal_original_sphere_cut hR heR (hB.trans interior_subset) bB hRc
  have hgi : InjOn (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space := by
    intro x hx y hy hxy
    have heq : H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ :=
      Subtype.ext ((hg ⟨x,hx⟩).symm.trans (hxy.trans (hg ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.symm.injective heq)
  have hreal : ∀ x ∈ R,
      f x ∈ K.space ∧ (g (f x) : LatticeHandleAmbient ι κ L) = x := by
    intro x hx
    have hh := hH ⟨x,hx⟩
    refine ⟨hh ▸ (H ⟨x,hx⟩).property, ?_⟩
    rw [←hh,hg]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x,hx⟩)
  rcases hm with hm | ⟨ν,hν,c,hno,hmax,_⟩
  · obtain ⟨n,S,sS,_,_,hSf⟩ := hm.exists_boundary_spheres hR.isClosed K
      (fun z => (g z : LatticeHandleAmbient ι κ L)) hgPL hgi hreal
    obtain ⟨x,hx⟩ := (bD.isConnected_closed_complement_frontier he hdim hi).nonempty
    obtain ⟨i,hiS⟩ := mem_iUnion.mp (hSf.subset hx)
    exact False.elim (bD.no_sphere_in_exterior_frontier he hdim hi
      ((subset_iUnion S i).trans hSf.symm.subset) ⟨sS i⟩)
  let := hν
  refine ⟨t,f,K,H,g,hf,hfi,hK,hH,hg,hgPL,ν,hν,c,hno,hmax,?_⟩
  intro T sT hT
  obtain ⟨d,x,hdS,hdO,hdB,hdC,hdinside,hx,hpunctured⟩ :=
    c.exists_punctured_extension f hmax sT hT isOpen_univ (subset_univ T)
  have hdinside' := hdinside.trans inter_subset_right
  obtain ⟨_,_,_,haway,hfront⟩ := d.punctured_component_port_boundary
    (fun S s hS => bD.no_sphere_in_exterior_frontier he hdim hi hS ⟨s⟩) K (fun z => (g z : LatticeHandleAmbient ι κ L)) hgPL hgi hreal hx hpunctured
  exact ⟨d,x,hdS,hdO,hdB,hdC,hdinside',hx,hpunctured,haway,hfront,
    c.exists_new_port_subset_of_punctured_component d hdC hdinside' hno hx hpunctured⟩

end PoincareConjecture.M76
