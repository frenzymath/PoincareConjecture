import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ProtectedDomainSphereBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.MaximalCutExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedExtensionPorts
import Mathlib.Data.Nat.Find












set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem exists_maximal_original_sphere_cut
    {X : Type u} {ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) (hRc : IsConnected R) :
    ∃ (t : Finset R) (f : X → (t → ℝ × V3))
      (K : SimplicialComplex ℝ (t → ℝ × V3)) (H : R ≃ₜ K.space)
      (g : (t → ℝ × V3) → R),
      (∀ j,LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target) ∧ InjOn f R ∧
      K.faces.Finite ∧ (∀ x : R,(H x : t → ℝ × V3) = f x) ∧
      (∀ z : K.space,(g z : X) = H.symm z) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (HasPuncturedSphereModel e f R ∨
        ∃ (κ : Type u) (_ : Fintype κ) (c : MarkedSphereCut e R κ),
          HasNoPuncturedSphereComponents e f c.carrier ∧
          (∀ (ν : Type u) [Fintype ν] (d : MarkedSphereCut e R ν),
            HasNoPuncturedSphereComponents e f d.carrier →
              Fintype.card ν ≤ Fintype.card κ) ∧
          ∀ (T : Set X),ChartwisePLSphere e T → T ⊆ interior c.carrier →
            ∃ (d : MarkedSphereCut e R (Option κ)) (x : X),
              d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
              (∀ i,d.collar (some i) = c.collar i) ∧
              (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
              d.carrier = c.carrier \ d.collar none ∧
              closure (d.collar none) ⊆ interior c.carrier ∧
              x ∈ d.carrier ∧
              HasPuncturedSphereModel e f (connectedComponentIn d.carrier x) ∧
              ∃ b : Bool,d.ports (none,b) ⊆ connectedComponentIn d.carrier x) := by
  classical
  obtain ⟨t,f,K,_,H,g,_,hf,hK,_,_,_,_,_,hH,_,hg,hgPL,_⟩ :=
    exists_protected_pure_domain_model hR he hDR b
  have hfi : InjOn f R := by
    intro x hx y hy hxy
    have hEq : H ⟨x,hx⟩ = H ⟨y,hy⟩ := Subtype.ext
      ((hH ⟨x,hx⟩).trans (hxy.trans (hH ⟨y,hy⟩).symm))
    exact congrArg Subtype.val (H.injective hEq)
  refine ⟨t,f,K,H,g,hf,hfi,hK,hH,hg,hgPL,?_⟩
  by_cases hpunctured : HasPuncturedSphereModel e f R
  · exact Or.inl hpunctured
  right
  obtain ⟨N,hN⟩ := exists_protected_domain_sphere_bound hR he hDR b hRc
  have hbound {κ : Type u} [Fintype κ] (c : MarkedSphereCut e R κ)
      (hc : HasNoPuncturedSphereComponents e f c.carrier) : Fintype.card κ + 1 ≤ N :=
    hN (t → ℝ × V3) κ f hf hfi c.spheres c.spherePL c.sphereInterior c.sphereDisjoint
      c.collar c.product c.compactCut c.plCut c.collarOpen c.collarInterior c.collarDisjoint
      c.openCoordinates c.centerCoordinates c.sphereClosure c.ports c.portPL c.portDisjoint
      c.portClosure c.frontierCut hc
  let P : ℕ → Prop := fun n => ∃ (κ : Type u) (_ : Fintype κ)
    (c : MarkedSphereCut e R κ), Fintype.card κ = n ∧
      HasNoPuncturedSphereComponents e f c.carrier
  have hzero : P 0 := by
    let κ : Type u := ULift.{u} Empty
    let S : κ → Set X := fun _ => ∅
    obtain ⟨c,_,_⟩ := exists_marked_sphere_cut S
      (fun i => i.down.elim) (fun i => i.down.elim)
      hR he (fun i => i.down.elim) isOpen_univ (fun _ => subset_univ _)
    have hcarrier : c.carrier = R := by simp [MarkedSphereCut.carrier]
    refine ⟨κ,inferInstance,c,by simp [κ],?_⟩
    rw [hcarrier]
    intro x hx
    simpa only [hRc.isPreconnected.connectedComponentIn hx] using hpunctured
  obtain ⟨κ,hκ,c,hcard,hno⟩ := Nat.findGreatest_spec (Nat.zero_le N) hzero
  let := hκ
  have hmax : ∀ (ν : Type u) [Fintype ν] (d : MarkedSphereCut e R ν),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card ν ≤ Fintype.card κ := by
    intro ν _ d hd
    rw [hcard]
    exact Nat.le_findGreatest (by have h := hbound d hd; omega)
      (show P (Fintype.card ν) from ⟨ν,inferInstance,d,rfl,hd⟩)
  refine ⟨κ,hκ,c,hno,hmax,?_⟩
  intro T sT hT
  obtain ⟨d,x,hS,hO,hB,hcarrier,hclosed,hx,hmodel⟩ :=
    c.exists_punctured_extension f hmax sT hT isOpen_univ (subset_univ T)
  have hinside := hclosed.trans inter_subset_right
  exact ⟨d,x,hS,hO,hB,hcarrier,hinside,hx,hmodel,
    c.exists_new_port_subset_of_punctured_component d hcarrier hinside hno hx hmodel⟩

end PoincareConjecture.M76
