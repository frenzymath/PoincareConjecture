import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawSphereCutComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalCutHomologyRetract
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false
open Set
open scoped Topology
namespace PoincareConjecture.M76

theorem exists_deformation_component_homotopyEquiv
    {X : Type*} [TopologicalSpace X] (U Q : Set X) (hQU : Q ⊆ U)
    (F : C(unitInterval × U, U)) (hF0 : ∀x, F (0,x) = x)
    (hF1 : ∀x, (F (1,x) : X) ∈ Q)
    (hfix : ∀t (x : U), (x : X) ∈ Q → F (t,x) = x) (x : U) :
    ∃ q : Q, (q : X) ∈ connectedComponentIn U x ∧
      connectedComponentIn Q q = connectedComponentIn U x ∩ Q ∧
      ∃ e : ContinuousMap.HomotopyEquiv (connectedComponentIn U x) (connectedComponentIn Q q),
        ∀y, (e.invFun y : X) = y := by
  classical
  have hpath (t : unitInterval) (y : U) :
      (F (t,y) : X) ∈ connectedComponentIn U y := by
    let p : unitInterval → X := fun t => F (t,y)
    have hp : Continuous p := continuous_subtype_val.comp
      (F.continuous.comp (continuous_id.prodMk continuous_const))
    have hsub := (isConnected_range hp).isPreconnected.subset_connectedComponentIn
      (show (y : X) ∈ range p from ⟨0,congrArg Subtype.val (hF0 y)⟩)
      (show range p ⊆ U by rintro _ ⟨t,rfl⟩; exact (F (t,y)).property)
    exact hsub ⟨t,rfl⟩
  let r : X → X := fun y => if hy : y ∈ U then (F (1,⟨y,hy⟩) : X) else y
  have hr (y : U) : r y = (F (1,y) : X) := by simp only [r,dif_pos y.property]
  have hrc : ContinuousOn r U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : U.domRestrict r = fun y : U => (F (1,y) : X) := funext hr
    rw [he]
    exact continuous_subtype_val.comp (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hrQ : MapsTo r U Q := fun y hy => (hr ⟨y,hy⟩).symm ▸ hF1 ⟨y,hy⟩
  have hrfix : EqOn r id Q := by
    intro y hy
    rw [hr ⟨y,hQU hy⟩,hfix 1 _ hy]
    rfl
  let q : Q := ⟨F (1,x),hF1 x⟩
  have hqx : (q : X) ∈ connectedComponentIn U x := hpath 1 x
  have hcomponent : connectedComponentIn Q q = connectedComponentIn U x ∩ Q := by
    apply Subset.antisymm
    · have hh := connectedComponentIn_mono (q : X) hQU
      rw [← connectedComponentIn_eq hqx] at hh
      exact subset_inter hh (connectedComponentIn_subset _ _)
    · rintro y ⟨hy,hyQ⟩
      have him := hrc.mapsTo_connectedComponentIn x.property hy
      have hh := connectedComponentIn_mono (r x) (mapsTo_iff_image_subset.mp hrQ) him
      simpa only [hr x,hrfix hyQ,id_eq,q] using hh
  have hstay (t : unitInterval) (y : connectedComponentIn U (x : X)) :
      (F (t,⟨y,connectedComponentIn_subset _ _ y.property⟩) : X) ∈ connectedComponentIn U x := by
    have hh := hpath t ⟨y,connectedComponentIn_subset _ _ y.property⟩
    rwa [← connectedComponentIn_eq y.property] at hh
  let inc : C(connectedComponentIn Q (q : X),connectedComponentIn U (x : X)) :=
    ⟨fun y => ⟨y,(hcomponent.subset y.property).1⟩,continuous_subtype_val.subtype_mk _⟩
  let ret : C(connectedComponentIn U (x : X),connectedComponentIn Q (q : X)) :=
    ⟨fun y => ⟨F (1,⟨y,connectedComponentIn_subset _ _ y.property⟩),
      hcomponent.symm.subset ⟨hstay 1 y,hF1 _⟩⟩,
      (continuous_subtype_val.comp (F.continuous.comp
        (continuous_const.prodMk (continuous_subtype_val.subtype_mk _)))).subtype_mk _⟩
  have H : (ContinuousMap.id (connectedComponentIn U (x : X))).Homotopy (inc.comp ret) :=
    { toFun := fun z => ⟨F (z.1,⟨z.2,connectedComponentIn_subset _ _ z.2.property⟩),hstay z.1 z.2⟩
      continuous_toFun := (continuous_subtype_val.comp (F.continuous.comp
        (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))).subtype_mk _
      map_zero_left := fun y => Subtype.ext (congrArg (fun z : U => (z : X))
        (hF0 ⟨y,connectedComponentIn_subset _ _ y.property⟩))
      map_one_left := fun _ => rfl }
  have he : ret.comp inc = ContinuousMap.id (connectedComponentIn Q (q : X)) := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    exact congrArg (fun z : U => (z : X)) (hfix 1
      ⟨y,hQU (connectedComponentIn_subset _ _ y.property)⟩
      (connectedComponentIn_subset _ _ y.property))
  refine ⟨q,hqx,hcomponent,{toFun := ret, invFun := inc,left_inv := ⟨H.symm⟩,right_inv := ?_},fun _ => rfl⟩
  rw [he]

theorem exists_raw_cut_component_homotopyEquiv
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {A : κ → Type*} [∀i,TopologicalSpace (A i)]
    (R Q : Set X) (O S : κ → Set X)
    (W : ∀i,(A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃i,O i) (hcQ : IsClosed Q)
    (hCR : ∀i,closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀i z,(W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀i z,(W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC : ∀i,S i ⊆ closure (O i)) (x : (R \ ⋃i,S i : Set X)) :
    ∃ q : Q, (q : X) ∈ connectedComponentIn (R \ ⋃i,S i) x ∧
      connectedComponentIn Q q = connectedComponentIn (R \ ⋃i,S i) x ∩ Q ∧
      ∃ e : ContinuousMap.HomotopyEquiv
        (connectedComponentIn (R \ ⋃i,S i) x) (connectedComponentIn Q q),
        ∀y, (e.invFun y : X) = y := by
  have hQU : Q ⊆ R \ ⋃i,S i := by
    intro y hy
    have hy' := hQ.subset hy
    refine ⟨hy'.1,?_⟩
    intro hs
    obtain ⟨i,hi⟩ := mem_iUnion.mp hs
    let z := (W i).symm ⟨y,hSC i hi⟩
    have hWz : (W i z : X) = y := congrArg Subtype.val ((W i).apply_symm_apply _)
    have ht : (z.2 : ℝ) = 1/2 := (hS i z).mp (hWz.symm ▸ hi)
    exact hy'.2 (mem_iUnion.mpr ⟨i,hWz ▸ (hO i z).mpr (by rw [ht]; norm_num)⟩)
  obtain ⟨F,hF0,hF1,hfix⟩ := exists_raw_sphere_cut_retraction R Q O S W hQ hcQ hCR hdis hO hS hSC
  exact exists_deformation_component_homotopyEquiv _ Q hQU F hF0 hF1 hfix x

end PoincareConjecture.M76
