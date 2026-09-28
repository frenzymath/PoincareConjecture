import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PrescribedCutIncidenceCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedCollarPorts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedComponentDomains

set_option autoImplicit false
open Set Metric Geometry CategoryTheory
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem exists_prescribed_collar_zero_component_count
    {X κ : Type u} {ι : Type*} [TopologicalSpace X] [T2Space X]
    [Fintype κ] [DecidableEq κ] {e : ι → OpenPartialHomeomorph X V3}
    (R Q : Set X) (hR : IsCompact R) (hRPL : PLDomain e R) (hRc : IsConnected R)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (O : κ → Set X) (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (hQeq : Q = R \ ⋃ i,O i) (hQ : IsCompact Q) (hQPL : PLDomain e Q)
    (hO : ∀ i, IsOpen (O i)) (hCR : ∀ i, closure (O i) ⊆ R)
    (hCC : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hstrip : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    ∃ D : ConnectedComponents Q → Set X,
      (∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x) ∧
      Fintype.card κ + 1 ≤ Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
        {v | Limits.IsZero (ModTwoMayerVietoris.homology (D v) 1)}.ncard := by
  classical
  obtain ⟨B,H,hW,hincQ,hBfront,hcover⟩ := exists_prescribed_cut_collar_ports O W hQeq hCR hCC hstrip
  have hBconn (b : κ × Bool) : IsConnected (B b) := by
    let : ConnectedSpace (S b.1) := (sS b.1).parametrization.connectedSpace_iff.mp
      (isConnected_iff_connectedSpace.mp (isConnected_sphere (by simp) (0 : V3) zero_le_one))
    let : ConnectedSpace (B b) := (H b.1 b.2).connectedSpace_iff.mp inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  obtain ⟨hfin,D,owner,hD,hDD,hDcover,howner,hother,hactual⟩ :=
    exists_marked_pl_component_domains hQ hQPL B hBconn hBfront
  let := hfin
  let : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
  let ends := fun i b => owner (i,b)
  have hinc (i) (v) : closure (O i) ∩ D v = ⋃ b ∈ {b | ends i b = v}, B (i,b) := by
    apply subset_antisymm
    · rintro x ⟨hxC,hxD⟩
      have hxQ : x ∈ Q := (hD v).2.2.2.1 hxD
      have hxB := (hincQ i).subset ⟨hxC,hxQ⟩
      have hb : ∃ b : Bool, x ∈ B (i,b) := by
        rcases hxB with hxB | hxB
        · exact ⟨false,hxB⟩
        · exact ⟨true,hxB⟩
      obtain ⟨b,hb⟩ := hb
      have he : ends i b = v := by
        by_contra hne
        exact disjoint_left.mp (hother (i,b) v hne) hb hxD
      exact mem_iUnion₂.mpr ⟨b,he,hb⟩
    · intro x hx
      obtain ⟨b,hb,hxB⟩ := mem_iUnion₂.mp hx
      have hxC : x ∈ closure (O i) :=
        ((hincQ i).symm.subset (by cases b <;> simp_all)).1
      exact ⟨hxC,(howner (i,b) v).mpr hb hxB⟩
  refine ⟨D,hactual,?_⟩
  exact prescribed_cut_card_le_homology_add_zero_components R Q hR hRPL hRc S sS O B H W D ends
    hQeq hQ.isClosed hO hCR hCC hcover
    (fun v => ⟨(hD v).1,(hD v).2.1,(hD v).2.2.1,(hD v).2.2.2.1⟩)
    hDD hDcover hactual hinc hW

end PoincareConjecture.M76
