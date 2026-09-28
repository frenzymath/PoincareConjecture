import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedSphereCut

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_extension_with_original_collar
    {X ι κ : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R T U : Set X}
    (c : MarkedSphereCut e R κ) (sT : ChartwisePLSphere e T)
    (hT : T ⊆ interior c.carrier) (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ d : MarkedSphereCut e R (Option κ),
      d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
      (∀ i,d.collar (some i) = c.collar i) ∧
      (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
      d.carrier = c.carrier \ d.collar none ∧
      closure (d.collar none) ⊆ U ∩ interior c.carrier ∧
      Nonempty (OriginalFiniteSphereCollar e c.carrier T (d.collar none)
        (fun b => d.ports (none,b))) ∧
      ∀ (b : Bool) (A : Set X), ChartwisePLBall e A (d.ports (none,b)) →
        A ⊆ d.carrier → ∃ A', Nonempty (ChartwisePLBall e A' T) ∧
          A ⊆ interior A' ∧ A' ⊆ A ∪ closure (d.collar none) ∧ A' ⊆ c.carrier := by
  obtain ⟨Q,N,B,H,sB,W,_,hraw,htransfer,hQ,hQR,hQc,hQPL,hN,hNc,hNconn,hNin,hcross,hCC,
      hcontact,hBB,hfront,_,hW,hcenter,hopen,hTcenter,hTN,_⟩ :=
    exists_retained_sphere_cut_with_original_collar c.collar rfl c.collarDisjoint c.compactCut c.plCut
      sT hT hU hTU
  let S : Option κ → Set X := fun i => i.elim T c.spheres
  let O : Option κ → Set X := fun i => i.elim N c.collar
  let P : Option κ × Bool → Set X := fun b => b.1.elim (B b.2) (fun i => c.ports (i,b.2))
  let J : ∀ b,S b.1 ≃ₜ P b := fun b => by
    rcases b with ⟨i,b⟩
    cases i with
    | none => exact H b
    | some i => exact c.portMap (i,b)
  let V : ∀ i,(S i × unitInterval) ≃ₜ closure (O i) := fun i => by
    cases i with
    | none => exact W
    | some i => exact c.product i
  have hBcl (b : Bool) : B b ⊆ closure N := by
    intro x hx
    apply (hcontact.symm.subset _).1
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hSdis : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact (hcross j).mono hTN (c.sphereClosure j)
    | some i =>
      cases j with
      | none => exact ((hcross i).mono hTN (c.sphereClosure i)).symm
      | some j => exact c.sphereDisjoint (fun h => hij (congrArg some h))
  have hPdis : Pairwise fun i j => Disjoint (P i) (P j) := by
    rintro ⟨i,b⟩ ⟨j,d⟩ hij
    cases i with
    | none =>
      cases j with
      | none => exact hBB (fun h => hij (by cases h; rfl))
      | some j => exact (hcross j).mono (hBcl b) (c.portClosure (j,d))
    | some i =>
      cases j with
      | none => exact ((hcross i).mono (hBcl d) (c.portClosure (i,b))).symm
      | some j => exact c.portDisjoint (fun h => hij (by cases h; rfl))
  have hOunion : (⋃ i,O i) = (⋃ i,c.collar i) ∪ N := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      cases i with
      | none => exact Or.inr hi
      | some i => exact Or.inl (mem_iUnion.mpr ⟨i,hi⟩)
    · rintro (hx | hx)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨some i,hi⟩
      · exact mem_iUnion.mpr ⟨none,hx⟩
  have hQ' : (R \ ⋃ i,O i) = Q := by rw [hOunion,←hQR]
  have hPunion : (⋃ i,P i) = (⋃ i,c.ports i) ∪ ⋃ b,B b := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i,b⟩,hi⟩ := mem_iUnion.mp hx
      cases i with
      | none => exact Or.inr (mem_iUnion.mpr ⟨b,hi⟩)
      | some i => exact Or.inl (mem_iUnion.mpr ⟨(i,b),hi⟩)
    · rintro (hx | hx)
      · obtain ⟨⟨i,b⟩,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨(some i,b),hi⟩
      · obtain ⟨b,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨(none,b),hi⟩
  have hQfront : frontier (R \ ⋃ i,O i) = frontier R ∪ ⋃ i,P i := by
    rw [hQ',hfront,c.frontierCut,hPunion,union_assoc]
  refine ⟨{
    spheres := S
    spherePL := ?_
    sphereInterior := ?_
    sphereDisjoint := hSdis
    collar := O
    product := V
    collarOpen := ?_
    collarInterior := ?_
    collarDisjoint := hCC
    openCoordinates := ?_
    centerCoordinates := ?_
    sphereClosure := ?_
    ports := P
    portMap := J
    portPL := ?_
    portDisjoint := hPdis
    portClosure := ?_
    collarContact := ?_
    endpoints := ?_
    center := ?_
    compactCut := hQ'.symm ▸ hQc
    plCut := hQ'.symm ▸ hQPL
    frontierCut := hQfront },rfl,(fun _ => rfl),(fun _ _ => rfl),?_,hNin,hraw,?_⟩
  · intro i
    cases i
    · exact sT
    · exact c.spherePL _
  · intro i
    cases i
    · exact hT.trans (interior_mono sdiff_subset)
    · exact c.sphereInterior _
  · intro i
    cases i
    · exact hN
    · exact c.collarOpen _
  · intro i
    cases i
    · exact hNin.trans (inter_subset_right.trans (interior_mono sdiff_subset))
    · exact c.collarInterior _
  · intro i
    cases i
    · exact hopen
    · exact c.openCoordinates _
  · intro i
    cases i
    · exact hTcenter
    · exact c.centerCoordinates _
  · intro i
    cases i
    · exact hTN
    · exact c.sphereClosure _
  · rintro ⟨i,b⟩
    cases i
    · exact sB b
    · exact c.portPL _
  · rintro ⟨i,b⟩
    cases i
    · exact hBcl b
    · exact c.portClosure _
  · intro i
    cases i with
    | none => exact hQ'.symm ▸ hcontact
    | some i =>
      change closure (c.collar i) ∩ (R \ ⋃ i,O i) = _
      rw [hQ',hQ]
      ext x
      constructor
      · exact fun hx => (c.collarContact i).subset ⟨hx.1,hx.2.1⟩
      · intro hx
        obtain ⟨hxO,hxQ⟩ := (c.collarContact i).symm.subset hx
        exact ⟨hxO,hxQ,fun hn => disjoint_left.mp (hcross i) (subset_closure hn) hxO⟩
  · intro i
    cases i
    · exact hW
    · exact c.endpoints _
  · intro i
    cases i
    · exact hcenter
    · exact c.center _
  · exact hQ'.trans hQ
  · intro b A ball hA
    apply htransfer b A ball
    exact hA.trans hQ'.subset

theorem MarkedSphereCut.exists_extension_with_endpoint_transfer
    {X ι κ : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R T U : Set X}
    (c : MarkedSphereCut e R κ) (sT : ChartwisePLSphere e T)
    (hT : T ⊆ interior c.carrier) (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ d : MarkedSphereCut e R (Option κ),
      d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
      (∀ i,d.collar (some i) = c.collar i) ∧
      (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
      d.carrier = c.carrier \ d.collar none ∧
      closure (d.collar none) ⊆ U ∩ interior c.carrier ∧
      ∀ (b : Bool) (A : Set X), ChartwisePLBall e A (d.ports (none,b)) →
        A ⊆ d.carrier → ∃ A', Nonempty (ChartwisePLBall e A' T) ∧
          A ⊆ interior A' ∧ A' ⊆ A ∪ closure (d.collar none) ∧ A' ⊆ c.carrier := by
  obtain ⟨d, hS, hO, hP, hQ, hN, _, htransfer⟩ :=
    c.exists_extension_with_original_collar sT hT hU hTU
  exact ⟨d, hS, hO, hP, hQ, hN, htransfer⟩

theorem MarkedSphereCut.exists_extension
    {X ι κ : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R T U : Set X}
    (c : MarkedSphereCut e R κ) (sT : ChartwisePLSphere e T)
    (hT : T ⊆ interior c.carrier) (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ d : MarkedSphereCut e R (Option κ),
      d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
      (∀ i,d.collar (some i) = c.collar i) ∧
      (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
      d.carrier = c.carrier \ d.collar none ∧
      closure (d.collar none) ⊆ U ∩ interior c.carrier := by
  obtain ⟨d, hS, hO, hP, hQ, hN, _⟩ :=
    c.exists_extension_with_endpoint_transfer sT hT hU hTU
  exact ⟨d, hS, hO, hP, hQ, hN⟩

end PoincareConjecture.M76
