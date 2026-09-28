import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3NestedRelativeBoundary

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.noPuncturedSphereComponents_mono
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}
    (c d : MarkedSphereCut e R κ) (hs : d.spheres = c.spheres)
    (hcarrier : c.carrier ⊆ d.carrier) (hR : IsClosed R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f c.carrier) :
    HasNoPuncturedSphereComponents e f d.carrier := by
  let cuts : Bool → MarkedSphereCut e R κ := fun b => if b then d else c
  let A (i : κ) : c.spheres i ≃ₜ d.spheres i := Homeomorph.setCongr (congrFun hs i).symm
  let W : ∀ b i, (c.spheres i × unitInterval) ≃ₜ closure ((cuts b).collar i) :=
    fun b i => by
      cases b
      · exact c.product i
      · exact (Homeomorph.prodCongr (A i) (Homeomorph.refl unitInterval)).trans (d.product i)
  have hQ (b : Bool) : (cuts b).carrier = R \ ⋃ i, (cuts b).collar i := rfl
  have hO (b : Bool) (i : κ) (z : c.spheres i × unitInterval) :
      (W b i z : X) ∈ (cuts b).collar i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1 := by
    cases b
    · exact c.openCoordinates i z
    · exact d.openCoordinates i (A i z.1, z.2)
  have hS (b : Bool) (i : κ) (z : c.spheres i × unitInterval) :
      (W b i z : X) ∈ c.spheres i ↔ (z.2 : ℝ) = 1/2 := by
    cases b
    · exact c.centerCoordinates i z
    · exact ((Set.ext_iff.mp (congrFun hs i) _).symm).trans
        (d.centerCoordinates i (A i z.1, z.2))
  have hSC (b : Bool) (i : κ) : c.spheres i ⊆ closure ((cuts b).collar i) := by
    cases b
    · exact c.sphereClosure i
    · exact (congrFun hs i).symm.subset.trans (d.sphereClosure i)
  exact hno.mono_original_collar_cut_relative_boundary R hR
    (fun b => (cuts b).carrier) (fun b => (cuts b).collar) c.spheres W hQ
    (fun b => (cuts b).compactCut) (fun b => (cuts b).plCut)
    (fun b => (cuts b).collarInterior) (fun b => (cuts b).collarDisjoint)
    hO hS hSC (fun b => (cuts b).ports) (fun b => (cuts b).portPL)
    (fun b => (cuts b).portDisjoint) (fun b => (cuts b).portClosure)
    (fun b => (cuts b).frontierCut) hcarrier K g hg hgi hreal

theorem MarkedSphereCut.exists_finer_noPuncturedSphereComponents
    {X E ι κ : Type*} [MetricSpace X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R U : Set X}
    (c : MarkedSphereCut e R κ) (hR : IsCompact R) (he : PLDomain e R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    (hU : IsOpen U) (hSU : ∀ i, c.spheres i ⊆ U) :
    ∃ d : MarkedSphereCut e R κ,
      d.spheres = c.spheres ∧
      (∀ i, closure (d.collar i) ⊆ U ∩ ⋃ j, c.collar j) ∧
      c.carrier ⊆ d.carrier ∧ HasNoPuncturedSphereComponents e f d.carrier := by
  have hSopen (i : κ) : c.spheres i ⊆ c.collar i := by
    intro x hx
    have h := (c.openCoordinates i (⟨x, hx⟩, ⟨(1/2 : ℝ), by norm_num⟩)).mpr
      (by norm_num)
    rwa [c.center i ⟨x, hx⟩] at h
  have hU' : IsOpen (U ∩ ⋃ j, c.collar j) := hU.inter (isOpen_iUnion c.collarOpen)
  have hSU' (i : κ) : c.spheres i ⊆ U ∩ ⋃ j, c.collar j :=
    fun x hx => ⟨hSU i hx, mem_iUnion.mpr ⟨i, hSopen i hx⟩⟩
  obtain ⟨d, hs, hsmall⟩ := exists_marked_sphere_cut c.spheres c.spherePL
    c.sphereDisjoint hR he c.sphereInterior hU' hSU'
  have hcarrier : c.carrier ⊆ d.carrier := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hd
    obtain ⟨i, hi⟩ := mem_iUnion.mp hd
    exact hx.2 ((hsmall i (subset_closure hi)).2)
  exact ⟨d, hs, hsmall, hcarrier,
    c.noPuncturedSphereComponents_mono d hs hcarrier hR.isClosed K g hg hgi hreal hno⟩

end PoincareConjecture.M76
