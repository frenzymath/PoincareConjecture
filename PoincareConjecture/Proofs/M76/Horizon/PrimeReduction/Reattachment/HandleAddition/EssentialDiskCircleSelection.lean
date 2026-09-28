import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.DiskAvoidance
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76
local notation "P2" => (ℝ×ℝ)

theorem exists_innermost_eligible_polygon_disk
    {κ : Type*} [Finite κ]
    (n:κ→ℕ) (P:∀i,Polygon P2 (n i+3))
    (hP:∀i,(P i).HasSimplicialEdges) (hPi:∀i,Function.Injective (P i))
    (hdis:Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    {U:Set P2} (hgood:∃i,closure (P i).inside⊆U) :
    ∃i,closure (P i).inside⊆U ∧
      ∀j,i≠j → Disjoint (closure (P i).inside) ((P j).boundary ℝ) := by
  classical
  let Good := {i:κ // closure (P i).inside⊆U}
  have : Nonempty Good := by
    obtain ⟨i,hi⟩ := hgood
    exact ⟨⟨i,hi⟩⟩
  obtain ⟨A,hA⟩ := (finite_range (fun i:Good => closure (P i).inside)).isPWO.exists_minimal
    (range_nonempty (fun i:Good => closure (P i).inside))
  obtain ⟨i,rfl⟩ := hA.1
  refine ⟨i.val,i.property,?_⟩
  intro j hij
  rcases (P i).boundary_subset_inside_or_outside_of_disjoint (P j)
    (hP i) (hPi i) (hP j) (hPi j) (hdis hij) with hinside | houtside
  · have hsub := (P i).closure_inside_subset_inside_of_boundary_subset_inside (P j)
      (hP i) (hPi i) (hP j) (hPi j) hinside
    have hjgood : closure (P j).inside⊆U := hsub.trans (subset_closure.trans i.property)
    have hback : closure (P i).inside⊆closure (P j).inside :=
      hA.2 (mem_range_self (⟨j,hjgood⟩:Good)) (hsub.trans subset_closure)
    obtain ⟨x,hxb⟩ := ((P i).isConnected_boundary (hP i) (hPi i)).nonempty
    have hxcl : x∈closure (P i).inside := by
      rw [←(P i).frontier_inside (hP i) (hPi i)] at hxb
      exact frontier_subset_closure hxb
    exact ((hsub (hback hxcl)).1 hxb).elim
  · apply disjoint_left.mpr
    intro x hx hxj
    rw [(P i).closure_inside (hP i) (hPi i)] at hx
    exact hx (houtside hxj)

theorem exists_innermost_disk_avoiding_proper_arcs
    {κ α : Type*} [Finite κ]
    (n:κ→ℕ) (P:∀i,Polygon P2 (n i+3))
    (hP:∀i,(P i).HasSimplicialEdges) (hPi:∀i,Function.Injective (P i))
    (hdis:Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    {U:Set P2} (hgood:∃i,closure (P i).inside⊆U)
    (arcs:α→Set P2) (hconn:∀a,IsPreconnected (arcs a))
    (hends:∀a,∃x∈arcs a,x∉U)
    (hseparate:∀a i,Disjoint (arcs a) ((P i).boundary ℝ)) :
    ∃i,IsFinitePLBallPair P2 (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside⊆U ∧
      Disjoint (⋃a,arcs a) (closure (P i).inside) ∧
      closure (P i).inside∩((⋃a,arcs a)∪(⋃j,(P j).boundary ℝ))=(P i).boundary ℝ ∧
      Disjoint (P i).inside ((⋃a,arcs a)∪(⋃j,(P j).boundary ℝ)) := by
  obtain ⟨i,hiU,hi⟩ := exists_innermost_eligible_polygon_disk n P hP hPi hdis hgood
  have harc : Disjoint (⋃a,arcs a) (closure (P i).inside) := by
    apply disjoint_iUnion_left.mpr
    intro a
    apply Dehn.Annuli.disjoint_polygon_disk_of_connected_set (P i) (hP i) (hPi i)
      (hconn a) (hseparate a i)
    obtain ⟨x,hxa,hxU⟩ := hends a
    exact ⟨x,hxa,fun hx => hxU (hiU hx)⟩
  have hcircle : closure (P i).inside∩(⋃j,(P j).boundary ℝ)=(P i).boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hx,hxall⟩
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hxall
      by_cases hij : i=j
      · exact hij.symm ▸ hxj
      · exact (disjoint_left.mp (hi j hij) hx hxj).elim
    · intro x hx
      exact ⟨((P i).isFinitePLBallPair_closed_inside (hP i) (hPi i)).1 hx,
        mem_iUnion_of_mem i hx⟩
  have hinter : closure (P i).inside∩((⋃a,arcs a)∪(⋃j,(P j).boundary ℝ))=
      (P i).boundary ℝ := by
    rw [inter_union_distrib_left,harc.symm.inter_eq,empty_union,hcircle]
  refine ⟨i,(P i).isFinitePLBallPair_closed_inside (hP i) (hPi i),hiU,harc,hinter,?_⟩
  apply disjoint_left.mpr
  intro x hx hxall
  exact hx.1 (hinter.subset ⟨subset_closure hx,hxall⟩)

theorem exists_innermost_region_disk_of_mixed_contacts
    {κ:Type*} [Finite κ] (pieces:κ→Set P2)
    (hdis:Pairwise fun i j => Disjoint (pieces i) (pieces j))
    {Rim U:Set P2} (hRU:Disjoint Rim U)
    (hmodels:∀i,IsFinitePLBallPair ℝ (pieces i) (pieces i∩Rim) ∨
      ∃(n:ℕ)(P:Polygon P2 (n+3)),Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ=pieces i ∧ Disjoint (pieces i) Rim)
    (hgood:∃(i:κ)(n:ℕ)(P:Polygon P2 (n+3)),Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ=pieces i ∧ closure P.inside⊆U) :
    ∃(i:κ)(n:ℕ)(P:Polygon P2 (n+3)),Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ=pieces i ∧
      IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      closure P.inside⊆U ∧
      closure P.inside∩(⋃j,pieces j)=P.boundary ℝ ∧
      Disjoint P.inside (⋃j,pieces j) := by
  classical
  let C := {i:κ // Disjoint (pieces i) Rim}
  let A := {i:κ // ¬Disjoint (pieces i) Rim}
  have hcircles (i:C) : ∃(n:ℕ)(P:Polygon P2 (n+3)),Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ=pieces i := by
    rcases hmodels i with ha | ⟨n,P,hPi,hP,hPb,_⟩
    · obtain ⟨u,v,_,huv⟩ := ha.exists_boundary_eq_pair
      have hu := huv.symm.subset (show u∈({u,v}:Set P2) from Or.inl rfl)
      exact (disjoint_left.mp i.property hu.1 hu.2).elim
    · exact ⟨n,P,hPi,hP,hPb⟩
  choose n P hPi hP hPb using hcircles
  have hPdis:Pairwise fun i j:C => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ) := by
    intro i j hij
    rw [hPb i,hPb j]
    exact hdis (fun h => hij (Subtype.ext h))
  have hPgood:∃i:C,closure (P i).inside⊆U := by
    obtain ⟨i,m,Q,hQi,hQ,hQb,hQU⟩ := hgood
    have hi:Disjoint (pieces i) Rim := by
      apply disjoint_left.mpr
      intro x hxi hxr
      exact disjoint_left.mp hRU hxr
        (hQU ((Q.isFinitePLBallPair_closed_inside hQ hQi).1 (hQb.symm.subset hxi)))
    refine ⟨⟨i,hi⟩,?_⟩
    have hinside:(P ⟨i,hi⟩).inside=Q.inside := by
      unfold Polygon.inside
      rw [hPb,hQb]
    simpa only [hinside] using hQU
  have harcs (i:A) : IsFinitePLBallPair ℝ (pieces i) (pieces i∩Rim) := by
    rcases hmodels i with ha | ⟨_,_,_,_,_,hc⟩
    · exact ha
    · exact (i.property hc).elim
  have hends (i:A) : ∃x∈pieces i,x∉U := by
    obtain ⟨u,v,_,huv⟩ := (harcs i).exists_boundary_eq_pair
    have hu := huv.symm.subset (show u∈({u,v}:Set P2) from Or.inl rfl)
    exact ⟨u,hu.1,fun hxU => disjoint_left.mp hRU hu.2 hxU⟩
  have hsep (i:A)(j:C):Disjoint (pieces i) ((P j).boundary ℝ) := by
    rw [hPb]
    exact hdis (fun h => i.property (h.symm ▸ j.property))
  obtain ⟨i,hball,hiU,_,hinter,havoid⟩ := exists_innermost_disk_avoiding_proper_arcs
    n P hP hPi hPdis hPgood (fun i:A => pieces i)
    (fun i => (harcs i).isConnected.2) hends hsep
  have hunion:(⋃i:A,pieces i)∪(⋃i:C,(P i).boundary ℝ)=⋃i,pieces i := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion_of_mem i.val hi
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion_of_mem i.val ((hPb i).subset hi)
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases hc:Disjoint (pieces i) Rim
      · exact Or.inr (mem_iUnion_of_mem (⟨i,hc⟩:C) ((hPb ⟨i,hc⟩).symm.subset hi))
      · exact Or.inl (mem_iUnion_of_mem (⟨i,hc⟩:A) hi)
  exact ⟨i,n i,P i,hPi i,hP i,hPb i,hball,hiU,hunion ▸ hinter,hunion ▸ havoid⟩

end PoincareConjecture.M76
