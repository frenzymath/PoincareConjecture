import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.ResidualCompressionDecrease
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem marked_frontier_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B S U : Set X}
    (hN : IsCompact N) (hfront : frontier N = (N ∩ B) ∪ (S ∪ U))
    (hdisj : Disjoint S U) {j : V2 → X} (P : OriginalDiskProduct e N j)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    (hPB : MapsTo P.map (D ×ˢ I) Bᶜ)
    (hside : ∀ z ∈ D ×ˢ I, P.map z ∈ frontier N → P.map z ∈ S) :
    frontier P.cutCarrier =
      (P.cutCarrier ∩ B) ∪ ((S \ P.openStrip) ∪ P.endDisks) ∪ U ∧
      P.cutCarrier ∩ B = N ∩ B := by
  obtain ⟨_, _, hcutfront, _, _, _⟩ := P.cut_geometry hN hopen
  have hB (x : X) : x ∈ B → x ∉ P.openStrip := by
    intro hx
    rintro ⟨z, hz, rfl⟩
    exact hPB ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩ hx
  have hU (x : X) : x ∈ U → x ∉ P.openStrip := by
    intro hx
    rintro ⟨z, hz, rfl⟩
    have hzfull : z ∈ D ×ˢ I := ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact disjoint_left.mp hdisj
      (hside z hzfull (hfront.symm.subset (Or.inr (Or.inr hx)))) hx
  constructor
  · rw [hcutfront, hfront]
    ext x
    change ((((x ∈ N ∧ x ∈ B) ∨ (x ∈ S ∨ x ∈ U)) ∧ x ∉ P.openStrip) ∨
        x ∈ P.endDisks) ↔
      (((x ∈ N ∧ x ∉ P.openStrip) ∧ x ∈ B) ∨
        ((x ∈ S ∧ x ∉ P.openStrip) ∨ x ∈ P.endDisks)) ∨ x ∈ U
    have := hB x
    have := hU x
    tauto
  · ext x
    change ((x ∈ N ∧ x ∉ P.openStrip) ∧ x ∈ B) ↔ x ∈ N ∧ x ∈ B
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hB x h.2⟩, h.2⟩⟩

theorem marked_face_residual_complexity_decreases
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N S Snew Nold Nnew : Set X}
    (hN : IsCompact N) (he : PLDomain e N) (hS : S ⊆ frontier N)
    {j : V2 → X} (P : OriginalDiskProduct e N j)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    (hside : ∀ z ∈ D ×ˢ I, P.map z ∈ frontier N → P.map z ∈ S)
    (hnew : Snew = (S \ P.openStrip) ∪ P.endDisks) (hnewSub : Snew ⊆ Nnew)
    (rim : C(Q, S)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (oldModel : FrontierResidualModel e Nold S)
    (newModel : FrontierResidualModel e Nnew Snew) :
    newModel.complexity < oldModel.complexity := by
  let U := interior N ∪ S
  have hcut : U ∩ frontier N = S := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxf⟩
      · exact (disjoint_left.mp disjoint_interior_frontier hx hxf).elim
      · exact hx
    · exact fun hx => ⟨Or.inr hx, hS hx⟩
  have hsmall : MapsTo P.map (D ×ˢ I) U := by
    intro z hz
    by_cases hzf : P.map z ∈ frontier N
    · exact Or.inr (hside z hz hzf)
    · exact Or.inl ((mem_interior_iff_notMem_frontier (P.inside hz)).mpr hzf)
  have hcontain : S ∪ P.closedStrip ⊆ N := by
    apply union_subset (hS.trans he.closed.frontier_subset)
    rintro _ ⟨z, hz, rfl⟩
    exact P.inside ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  exact P.frontierResidualModel_complexity_decreases hcut hsmall
    (P.isOpen_lateral_image he.closed (by norm_num : (1 / 2 : ℝ) ≤ 1) hopen)
    hnew he hN hcontain hnewSub rim hrim hessential oldModel newModel

end PoincareConjecture.M76.OriginalDiskProduct
