import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryPartitionCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.RepairedDiskComponent

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_capped_boundary_partition_strict_decrease
    {X γ ρ η : Type*} [TopologicalSpace X] [Finite γ] [Finite ρ] [Finite η]
    {S B F D : Set X} (P : γ → Set X) (rim : ρ → Set X)
    (old : ρ → γ) (R cap : η → Set X)
    (hP : ∀ c, IsClosed (P c))
    (hPdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hPcover : S ∩ B ⊆ ⋃ c, P c) (hPS : ∀ c, P c ⊆ S)
    (c : γ) (hcap : ∀ k, IsClosed (cap k)) (hcontact : ∀ k, cap k ∩ S ⊆ P c)
    (hrim : ∀ i, IsConnected (rim i))
    (hrimsub : ∀ i, rim i ⊆ (S ∩ B) ∩ F)
    (hrimold : ∀ i, rim i ⊆ P (old i))
    (hrimdis : Pairwise fun i j => Disjoint (rim i) (rim j))
    (hR : ∀ k, IsClosed (R k ∩ F)) (hRS : ∀ k, R k ⊆ S)
    (hRcover : S ∩ F ⊆ ⋃ k, R k ∩ F)
    (hRdis : Pairwise fun k l => Disjoint (R k ∩ F) (R l ∩ F))
    {a b : ρ} (hab : a ≠ b) (hsame : old a = old b)
    (repair : η) (harepair : rim a ⊆ R repair)
    (hrepair : ∀ x ∈ rim a,
      connectedComponentIn ((R repair ∪ cap repair) ∩ B) x = D)
    (hDfront : D ∩ F = rim a) :
    ∃ (side : ρ → η) (point : ρ → X),
      (∀ i, point i ∈ rim i ∧ rim i ⊆ R (side i)) ∧
      side a = repair ∧
      ∀ selected : Set η,
        let retained := {i | side i ∈ selected}
        let label := fun i => (side i,
          connectedComponentIn ((R (side i) ∪ cap (side i)) ∩ B) (point i))
        retained.ncard - (label '' retained).ncard <
          Nat.card ρ - (Set.range old).ncard := by
  classical
  letI := Fintype.ofFinite ρ
  have hside (i : ρ) : ∃ k, rim i ⊆ R k ∩ F := by
    have hcover : rim i ⊆ ⋃ k, R k ∩ F := fun x hx =>
      hRcover ⟨(hrimsub i hx).1.1,(hrimsub i hx).2⟩
    obtain ⟨k,hk,_⟩ := (hrim i).exists_unique_subset_finite_disjoint_closed (fun k => R k ∩ F)
      (fun k => hR k) hRdis hcover
    exact ⟨k,hk⟩
  choose side hside using hside
  choose point hpoint using fun i => (hrim i).nonempty
  have hsideR (i : ρ) : rim i ⊆ R (side i) := fun x hx => (hside i hx).1
  have hrepairside : side a = repair := by
    by_contra hne
    exact disjoint_left.mp (hRdis hne) (hside a (hpoint a))
      ⟨harepair (hpoint a),(hrimsub a (hpoint a)).2⟩
  refine ⟨side,point,fun i => ⟨hpoint i,hsideR i⟩,hrepairside,?_⟩
  intro selected
  let retained := Finset.univ.filter (fun i => side i ∈ selected)
  let C := fun i => connectedComponentIn ((R (side i) ∪ cap (side i)) ∩ B) (point i)
  let label := fun i => (side i,C i)
  have hpointB (i : ρ) : point i ∈ (R (side i) ∪ cap (side i)) ∩ B :=
    ⟨Or.inl (hsideR i (hpoint i)),(hrimsub i (hpoint i)).1.2⟩
  have hrimC (i : ρ) : rim i ⊆ C i :=
    (hrim i).isPreconnected.subset_connectedComponentIn (hpoint i)
      (fun x hx => ⟨Or.inl (hsideR i hx),(hrimsub i hx).1.2⟩)
  have hCold (i : ρ) : C i ∩ S ⊆ P (old i) := by
    have hCconn : IsConnected (C i) := isConnected_connectedComponentIn_iff.mpr (hpointB i)
    have hCsub : C i ⊆ (S ∪ cap (side i)) ∩ B := by
      intro x hx
      obtain ⟨hxR | hxcap,hxB⟩ := connectedComponentIn_subset _ _ hx
      · exact ⟨Or.inl (hRS (side i) hxR),hxB⟩
      · exact ⟨Or.inr hxcap,hxB⟩
    obtain ⟨d,_,hd⟩ := exists_old_piece_for_capped_component P hP hPdis hPcover hPS
      c (hcap (side i)) (hcontact (side i)) hCconn hCsub
    have heq : d = old i := by
      by_contra hne
      exact disjoint_left.mp (hPdis hne)
        (hd ⟨hrimC i (hpoint i),(hrimsub i (hpoint i)).1.1⟩)
        (hrimold i (hpoint i))
    simpa only [heq] using hd
  have hrefine : ∀ i ∈ retained, ∀ j ∈ retained, label i = label j → old i = old j := by
    intro i hi j hj heq
    have hCC : C i = C j := congrArg Prod.snd heq
    by_contra hne
    exact disjoint_left.mp (hPdis hne) (hrimold i (hpoint i))
      (hCold j ⟨hCC ▸ hrimC i (hpoint i),(hrimsub i (hpoint i)).1.1⟩)
  have hCa : C a = D := by
    dsimp only [C]
    rw [hrepairside]
    exact hrepair (point a) (hpoint a)
  have hisolate : a ∈ retained → ∀ i ∈ retained, label i = label a → i = a := by
    intro ha i hi heq
    have hCC : C i = C a := congrArg Prod.snd heq
    have hxD : point i ∈ D := (hCC.trans hCa) ▸ hrimC i (hpoint i)
    have hxa : point i ∈ rim a := hDfront ▸ ⟨hxD,(hrimsub i (hpoint i)).2⟩
    by_contra hne
    exact disjoint_left.mp (hrimdis hne) (hpoint i) hxa
  have hlt := boundary_partition_excess_lt_of_isolated_rim Finset.univ retained
    (Finset.filter_subset _ _) old label hrefine (Finset.mem_univ a) (Finset.mem_univ b)
    hab hsame hisolate
  have hret : (retained : Set ρ) = {i | side i ∈ selected} := by
    ext i
    simp [retained]
  have hcard (U : Finset (η × Set X)) : U.card = (U : Set (η × Set X)).ncard := by simp
  have hrange : ((Finset.univ.image old : Finset γ) : Set γ) = Set.range old := by simp
  rw [←Set.ncard_coe_finset retained, hcard, Finset.coe_image, hret,
    ←Set.ncard_coe_finset (Finset.univ.image old), hrange, Finset.card_univ] at hlt
  simpa only [Nat.card_eq_fintype_card] using hlt

end PoincareConjecture.M76
