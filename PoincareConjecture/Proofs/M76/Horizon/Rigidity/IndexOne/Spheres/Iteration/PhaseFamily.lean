import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.ComponentDecrease
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.BallAvoidsAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.Classification
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Geometry













set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus




theorem exists_phase_family_after_closed_excision
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    {P A R K : Set X} {n : ℕ} (T : Fin n → Set X)
    (hcover : A ∪ (⋃ i, T i) = P)
    (hAcomp : ∀ x ∈ A, connectedComponentIn P x = A)
    (hAmeet : (A ∩ frontier R).Nonempty)
    (hpair : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hAdis : ∀ i, Disjoint A (T i))
    (hT : ∀ i, IsCompact (T i) ∧ IsConnected (T i) ∧ T i ⊆ P ∧
      (∀ x ∈ T i, connectedComponentIn P x = T i) ∧
      Disjoint (T i) (frontier R) ∧ Nonempty (ChartwisePLSphere e (T i)))
    (hK : IsClosed K) (hKR : K ⊆ interior R) (hfront : Disjoint P (frontier K)) :
    ∃ (m : ℕ) (U : Fin m → Set X) (index : Fin m → Fin n),
      m ≤ n ∧ Function.Injective index ∧ (∀ i, U i = T (index i)) ∧
      Disjoint K A ∧ A ⊆ P \ K ∧
      (∀ x ∈ A, connectedComponentIn (P \ K) x = A) ∧
      A ∪ (⋃ i, U i) = P \ K ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, Disjoint A (U i)) ∧
      (∀ i, IsCompact (U i) ∧ IsConnected (U i) ∧ U i ⊆ P \ K ∧
        (∀ x ∈ U i, connectedComponentIn (P \ K) x = U i) ∧
        Disjoint (U i) (frontier R) ∧ Nonempty (ChartwisePLSphere e (U i))) ∧
      (∀ i, (T i ∩ K).Nonempty → m < n) ∧
      (∀ i, T i ⊆ K → m < n) ∧
      ∀ x ∈ P \ K, connectedComponentIn (P \ K) x = connectedComponentIn P x := by
  classical
  have hAP : A ⊆ P := fun x hx => hcover.subset (Or.inl hx)
  have hAconn : IsPreconnected A := by
    obtain ⟨x, hxA, _⟩ := hAmeet
    rw [← hAcomp x hxA]
    exact isPreconnected_connectedComponentIn
  have hKA : Disjoint K A := Poincare.Topology.disjoint_of_meets_old_frontier
    hK hKR hAconn (hfront.mono_left hAP) hAmeet
  have hAnew : A ⊆ P \ K := fun x hx =>
    ⟨hAP hx, fun hxK => disjoint_left.mp hKA hxK hx⟩
  let remaining := {i : Fin n // Disjoint (T i) K}
  let equiv : Fin (Fintype.card remaining) ≃ remaining := (Fintype.equivFin remaining).symm
  let index (i : Fin (Fintype.card remaining)) : Fin n := (equiv i).val
  let U (i : Fin (Fintype.card remaining)) := T (index i)
  have hidx : Function.Injective index := by
    intro i j hij
    exact equiv.injective (Subtype.ext hij)
  have hretained (i : Fin (Fintype.card remaining)) : Disjoint (U i) K := (equiv i).property
  have hUnew (i : Fin (Fintype.card remaining)) : U i ⊆ P \ K := fun x hx =>
    ⟨(hT (index i)).2.2.1 hx, fun hxK => disjoint_left.mp (hretained i) hx hxK⟩
  have hcount : Fintype.card remaining ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => Disjoint (T i) K)
  have hstrict (i : Fin n) (hmeet : (T i ∩ K).Nonempty) :
      Fintype.card remaining < n := by
    have hnot : ¬ Disjoint (T i) K := by
      obtain ⟨x, hxT, hxK⟩ := hmeet
      exact fun h => disjoint_left.mp h hxT hxK
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_lt (p := fun i : Fin n => Disjoint (T i) K) hnot
  have hpoint {x : X} (hx : x ∈ P \ K) :
      connectedComponentIn (P \ K) x = connectedComponentIn P x :=
    Poincare.Topology.connectedComponentIn_sdiff_of_disjoint_frontier hK hfront hx
  refine ⟨Fintype.card remaining, U, index, hcount, hidx, fun _ => rfl,
    hKA, hAnew, ?_, ?_, ?_, ?_, ?_, hstrict, ?_, ?_⟩
  · intro x hx
    exact (hpoint (hAnew hx)).trans (hAcomp x hx)
  · apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact hAnew hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact hUnew i hi
    · rintro x ⟨hxP, hxK⟩
      rcases hcover.symm.subset hxP with hxA | hxT
      · exact Or.inl hxA
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxT
        have hi : Disjoint (T i) K := by
          rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier
              (hT i).2.1.isPreconnected hK (hfront.mono_left (hT i).2.2.1) with hin | hout
          · exact (hxK (interior_subset (hin hxi))).elim
          · exact hout
        refine Or.inr (mem_iUnion.mpr ⟨equiv.symm ⟨i, hi⟩, ?_⟩)
        change x ∈ T ((equiv (equiv.symm ⟨i, hi⟩)).val)
        rw [equiv.apply_symm_apply]
        exact hxi
  · intro i j hij
    exact hpair (fun h => hij (hidx h))
  · intro i
    exact hAdis (index i)
  · intro i
    obtain ⟨hc, hconn, _, hcomp, hrim, hsphere⟩ := hT (index i)
    exact ⟨hc, hconn, hUnew i, fun x hx => (hpoint (hUnew i hx)).trans (hcomp x hx),
      hrim, hsphere⟩
  · intro i hin
    obtain ⟨x, hx⟩ := (hT i).2.1.nonempty
    exact hstrict i ⟨x, hx, hin hx⟩
  · intro x hx
    exact hpoint hx



theorem exists_finite_connected_cover_decrease
    {X : Type*} [TopologicalSpace X] {P K : Set X} {n : ℕ}
    (T : Fin n → Set X) (hcover : (⋃ i, T i) = P)
    (hT : ∀ i, IsConnected (T i)) (hK : IsClosed K)
    (hfront : Disjoint P (frontier K)) (hmeet : (P ∩ K).Nonempty) :
    ∃ (m : ℕ) (U : Fin m → Set X),
      m < n ∧ (⋃ i, U i) = P \ K ∧ (∀ i, IsConnected (U i)) := by
  classical
  let remaining := {i : Fin n // Disjoint (T i) K}
  let equiv : Fin (Fintype.card remaining) ≃ remaining := (Fintype.equivFin remaining).symm
  let U (i : Fin (Fintype.card remaining)) := T (equiv i).val
  have hsub (i : Fin n) : T i ⊆ P :=
    fun x hx => hcover.subset (mem_iUnion.mpr ⟨i, hx⟩)
  have hstrict : Fintype.card remaining < n := by
    obtain ⟨x, hxP, hxK⟩ := hmeet
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm.subset hxP)
    have hnot : ¬ Disjoint (T i) K := fun h => disjoint_left.mp h hxi hxK
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_lt (p := fun i : Fin n => Disjoint (T i) K) hnot
  refine ⟨Fintype.card remaining, U, hstrict, ?_, fun i => hT (equiv i).val⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact ⟨hsub (equiv i).val hxi, fun hxK => disjoint_left.mp (equiv i).property hxi hxK⟩
  · rintro x ⟨hxP, hxK⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm.subset hxP)
    have hi : Disjoint (T i) K := by
      rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier
          (hT i).isPreconnected hK (hfront.mono_left (hsub i)) with hin | hout
      · exact (hxK (interior_subset (hin hxi))).elim
      · exact hout
    refine mem_iUnion.mpr ⟨equiv.symm ⟨i, hi⟩, ?_⟩
    change x ∈ T ((equiv (equiv.symm ⟨i, hi⟩)).val)
    rw [equiv.apply_symm_apply]
    exact hxi



theorem exists_finite_connected_cover_union
    {X : Type*} [TopologicalSpace X] {P Q : Set X} {n m : ℕ}
    (T : Fin n → Set X) (U : Fin m → Set X)
    (hTcover : (⋃ i, T i) = P) (hUcover : (⋃ i, U i) = Q)
    (hT : ∀ i, IsConnected (T i)) (hU : ∀ i, IsConnected (U i)) :
    ∃ V : Fin (n + m) → Set X, (⋃ i, V i) = P ∪ Q ∧ ∀ i, IsConnected (V i) := by
  let equiv : Fin (n + m) ≃ Fin n ⊕ Fin m := finSumFinEquiv.symm
  let V : Fin (n + m) → Set X := fun i => Sum.elim T U (equiv i)
  refine ⟨V, ?_, ?_⟩
  · change (⋃ i, (Sum.elim T U) (equiv i)) = P ∪ Q
    rw [equiv.surjective.iUnion_comp, iUnion_sumElim, hTcover, hUcover]
  · intro i
    rcases h : equiv i with j | j
    · simpa only [V, h, Sum.elim_inl] using hT j
    · simpa only [V, h, Sum.elim_inr] using hU j




theorem exists_finite_connected_cover_union_of_models
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X] [T2Space X]
    (K : Geometry.SimplicialComplex ℝ E) (J : Geometry.SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hJ : J.faces.Finite) {P Q : Set X}
    (HP : K.space ≃ₜ P) (HQ : J.space ≃ₜ Q)
    (f : X → E) (g : X → F) (hf : Continuous f) (hg : Continuous g)
    (hHP : ∀ x : P, (HP.symm x : E) = f x)
    (hHQ : ∀ x : Q, (HQ.symm x : F) = g x) :
    ∃ (n : ℕ) (T : Fin n → Set X), (⋃ i, T i) = P ∪ Q ∧
      ∀ i, IsConnected (T i) := by
  obtain ⟨n, T, hcover, _, hT⟩ :=
    exists_finite_source_components_of_model K hK HP f hf hHP
  obtain ⟨m, U, hcover', _, hU⟩ :=
    exists_finite_source_components_of_model J hJ HQ g hg hHQ
  obtain ⟨V, hV, hVconn⟩ := exists_finite_connected_cover_union T U hcover hcover'
    (fun i => (hT i).2.1) (fun i => (hU i).2.1)
  exact ⟨n + m, V, hV, hVconn⟩

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p



theorem PairedSourceGeometry.exists_finite_connected_phase_cover
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)} {a b : ℝ}
    (G : PairedSourceGeometry e phi a b)
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (ha : 0 < a) (hab : a < b) (hb : b < p) :
    ∃ (n : ℕ) (T : Fin n → Set X),
      (⋃ i, T i) = sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) ∧
      ∀ i, IsConnected (T i) := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have he := G.domains (a, b) (Or.inl rfl)
  have hfront := G.frontiers (a, b) (Or.inl rfl)
  have hAB := sourceSurface_disjoint_of_ordered_phases phi ha hab hb
  obtain ⟨s, f, K, _, HP, _, hf, _, _, hK, _, _, _, _, hHP, _⟩ :=
    exists_compressed_sourceSurface_incidence_model e d phi hphi F0 he hfront hAB
      (G.corners (a, b) (Or.inl rfl) a (Or.inl rfl))
  have hfront' : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier (latticeHandleDomain (Fin 1) (Fin 2) L)) ∪
        (sourceSurface phi (b : C) ∪ sourceSurface phi (a : C)) := by
    rw [hfront, union_comm (sourceSurface phi (a : C)) (sourceSurface phi (b : C))]
  obtain ⟨t, g, J, _, HQ, _, hg, _, _, hJ, _, _, _, _, hHQ, _⟩ :=
    exists_compressed_sourceSurface_incidence_model e d phi hphi F0 he hfront' hAB.symm
      (G.corners (a, b) (Or.inl rfl) b (Or.inr rfl))
  exact exists_finite_connected_cover_union_of_models K J hK hJ HP HQ f g hf hg hHP hHQ

end PoincareConjecture.M76.HamiltonIntervalTorus
