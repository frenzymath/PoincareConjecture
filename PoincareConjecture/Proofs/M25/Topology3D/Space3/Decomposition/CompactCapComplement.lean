import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Lattice.Fold











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D



theorem compact_connected_diff_of_connected_seam
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K D U : Set X}
    (hKcompact : IsCompact K) (hKconnected : IsConnected K)
    (hDcompact : IsCompact D) (hDK : D ⊆ K)
    (hUopen : IsOpen U) (hUD : U ⊆ D)
    (hseam : IsConnected (D \ U)) :
    IsCompact (K \ U) ∧ IsConnected (K \ U) ∧
      D ∩ (K \ U) = D \ U := by
  have hRcompact : IsCompact (K \ U) := hKcompact.diff hUopen
  have hseamR : D \ U ⊆ K \ U := fun _ hx => ⟨hDK hx.1, hx.2⟩
  refine ⟨hRcompact, ⟨hseam.nonempty.mono hseamR, ?_⟩, ?_⟩
  · apply (isPreconnected_iff_subset_of_fully_disjoint_closed hRcompact.isClosed).mpr
    have hstep : ∀ A B : Set X, IsClosed A → IsClosed B →
        K \ U ⊆ A ∪ B → Disjoint A B → D \ U ⊆ A →
        K \ U ⊆ A ∨ K \ U ⊆ B := by
      intro A B hA hB hcover hAB hseamA
      have hP : IsClosed (((K \ U) ∩ A) ∪ D) :=
        (hRcompact.isClosed.inter hA).union hDcompact.isClosed
      have hQ : IsClosed ((K \ U) ∩ B) := hRcompact.isClosed.inter hB
      have hPQ : Disjoint (((K \ U) ∩ A) ∪ D) ((K \ U) ∩ B) := by
        apply disjoint_left.mpr
        intro x hx hy
        rcases hx with hx | hx
        · exact disjoint_left.mp hAB hx.2 hy.2
        · exact disjoint_left.mp hAB (hseamA ⟨hx, hy.1.2⟩) hy.2
      have hKcover : K ⊆ (((K \ U) ∩ A) ∪ D) ∪ ((K \ U) ∩ B) := by
        intro x hx
        by_cases hxU : x ∈ U
        · exact Or.inl (Or.inr (hUD hxU))
        · rcases hcover ⟨hx, hxU⟩ with hxA | hxB
          · exact Or.inl (Or.inl ⟨⟨hx, hxU⟩, hxA⟩)
          · exact Or.inr ⟨⟨hx, hxU⟩, hxB⟩
      rcases (isPreconnected_iff_subset_of_fully_disjoint_closed
        hKcompact.isClosed).mp hKconnected.isPreconnected
          _ _ hP hQ hKcover hPQ with hKP | hKQ
      · left
        intro x hx
        rcases hKP hx.1 with hxP | hxD
        · exact hxP.2
        · exact hseamA ⟨hxD, hx.2⟩
      · exact Or.inr (fun _ hx => (hKQ hx.1).2)
    intro A B hA hB hcover hAB
    have hseamcover : D \ U ⊆ A ∪ B := hseamR.trans hcover
    have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp
      hseam.isPreconnected A B hA hB hseamcover
        (by rw [hAB.inter_eq, inter_empty])
    rcases hparts with hseamA | hseamB
    · exact hstep A B hA hB hcover hAB hseamA
    · exact (hstep B A hB hA (by simpa only [union_comm] using hcover)
        hAB.symm hseamB).symm
  · ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, hDK hx.1, hx.2⟩



theorem compact_connected_diff_finite_caps
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (K : Set X) (s : Finset ι) (D U : ι → Set X)
    (hKcompact : IsCompact K) (hKconnected : IsConnected K)
    (hDcompact : ∀ i ∈ s, IsCompact (D i))
    (hDK : ∀ i ∈ s, D i ⊆ K)
    (hUopen : ∀ i ∈ s, IsOpen (U i))
    (hUD : ∀ i ∈ s, U i ⊆ D i)
    (hseam : ∀ i ∈ s, IsConnected (D i \ U i))
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j)) :
    IsCompact (K \ ⋃ i ∈ s, U i) ∧
      IsConnected (K \ ⋃ i ∈ s, U i) ∧
      ∀ i ∈ s, D i ∩ (K \ ⋃ j ∈ s, U j) = D i \ U i := by
  classical
  have hinter : ∀ i ∈ s, D i ∩ (K \ ⋃ j ∈ s, U j) = D i \ U i := by
    intro i hi
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hxU
      exact hx.2.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxU⟩⟩)
    · intro hx
      refine ⟨hx.1, hDK i hi hx.1, ?_⟩
      intro hxU
      obtain ⟨j, hxU⟩ := mem_iUnion.mp hxU
      obtain ⟨hj, hxU⟩ := mem_iUnion.mp hxU
      by_cases hij : i = j
      · subst j
        exact hx.2 hxU
      · exact disjoint_left.mp (hdisjoint i hi j hj hij) hx.1 (hUD j hj hxU)
  suffices h : IsCompact (K \ ⋃ i ∈ s, U i) ∧
      IsConnected (K \ ⋃ i ∈ s, U i) from ⟨h.1, h.2, hinter⟩
  clear hinter
  revert hDcompact hDK hUopen hUD hseam hdisjoint
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _ _ _ _
    simpa using And.intro hKcompact hKconnected
  | @insert i s hi ih =>
    intro hDcompact hDK hUopen hUD hseam hdisjoint
    have hi' : i ∈ insert i s := Finset.mem_insert_self i s
    have hs : ∀ j ∈ s, j ∈ insert i s := fun _ hj => Finset.mem_insert_of_mem hj
    obtain ⟨hRcompact, hRconnected⟩ := ih
      (fun j hj => hDcompact j (hs j hj))
      (fun j hj => hDK j (hs j hj))
      (fun j hj => hUopen j (hs j hj))
      (fun j hj => hUD j (hs j hj))
      (fun j hj => hseam j (hs j hj))
      (fun j hj k hk hjk => hdisjoint j (hs j hj) k (hs k hk) hjk)
    have hDi : D i ⊆ K \ ⋃ j ∈ s, U j := by
      intro x hx
      refine ⟨hDK i hi' hx, ?_⟩
      intro hxU
      obtain ⟨j, hxU⟩ := mem_iUnion.mp hxU
      obtain ⟨hj, hxU⟩ := mem_iUnion.mp hxU
      have hij : i ≠ j := by
        rintro rfl
        exact hi hj
      exact disjoint_left.mp (hdisjoint i hi' j (hs j hj) hij)
        hx (hUD j (hs j hj) hxU)
    obtain ⟨hc, hn, _⟩ := compact_connected_diff_of_connected_seam
      hRcompact hRconnected (hDcompact i hi') hDi
      (hUopen i hi') (hUD i hi') (hseam i hi')
    have heq : ((K \ ⋃ j ∈ s, U j) \ U i) =
        K \ ⋃ j ∈ insert i s, U j := by
      ext x
      simp only [mem_sdiff, mem_iUnion, Finset.mem_insert]
      constructor
      · rintro ⟨⟨hxK, hxU⟩, hxi⟩
        refine ⟨hxK, ?_⟩
        rintro ⟨j, hj, hxj⟩
        rcases hj with rfl | hj
        · exact hxi hxj
        · exact hxU ⟨j, hj, hxj⟩
      · rintro ⟨hxK, hxU⟩
        refine ⟨⟨hxK, ?_⟩, ?_⟩
        · rintro ⟨j, hj, hxj⟩
          exact hxU ⟨j, Or.inr hj, hxj⟩
        · intro hxi
          exact hxU ⟨i, Or.inl rfl, hxi⟩
    rw [heq] at hc hn
    exact ⟨hc, hn⟩



theorem compact_connected_retained_of_cap_cover
    {X Y ι : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y]
    (K : Set X) (s : Finset ι) (D U : ι → Set X)
    (hKcompact : IsCompact K) (hKconnected : IsConnected K)
    (hDcompact : ∀ i ∈ s, IsCompact (D i))
    (hDK : ∀ i ∈ s, D i ⊆ K)
    (hUopen : ∀ i ∈ s, IsOpen (U i))
    (hUD : ∀ i ∈ s, U i ⊆ D i)
    (hseam : ∀ i ∈ s, IsConnected (D i \ U i))
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (j : X → Y) (hj : Function.Injective j) (hjcontinuous : ContinuousOn j K)
    (L : Set Y)
    (hcover : j '' K = L ∪ ⋃ i ∈ s, j '' D i)
    (hinter : ∀ i ∈ s, L ∩ (j '' D i) = j '' (D i \ U i)) :
    L = j '' (K \ ⋃ i ∈ s, U i) ∧ IsCompact L ∧ IsConnected L := by
  obtain ⟨hc, hn, _⟩ := compact_connected_diff_finite_caps K s D U
    hKcompact hKconnected hDcompact hDK hUopen hUD hseam hdisjoint
  have heq : L = j '' (K \ ⋃ i ∈ s, U i) := by
    ext y
    constructor
    · intro hy
      have hyK : y ∈ j '' K := by
        rw [hcover]
        exact Or.inl hy
      obtain ⟨x, hxK, rfl⟩ := hyK
      refine ⟨x, ⟨hxK, ?_⟩, rfl⟩
      intro hxU
      obtain ⟨i, hxU⟩ := mem_iUnion.mp hxU
      obtain ⟨hi, hxU⟩ := mem_iUnion.mp hxU
      have hxcap : j x ∈ L ∩ (j '' D i) :=
        ⟨hy, ⟨x, hUD i hi hxU, rfl⟩⟩
      rw [hinter i hi] at hxcap
      obtain ⟨z, hz, hzj⟩ := hxcap
      have hzx : z = x := hj hzj
      subst z
      exact hz.2 hxU
    · rintro ⟨x, hx, rfl⟩
      have hxcover : j x ∈ L ∪ ⋃ i ∈ s, j '' D i := by
        rw [← hcover]
        exact ⟨x, hx.1, rfl⟩
      rcases hxcover with hxL | hxcap
      · exact hxL
      · obtain ⟨i, hxcap⟩ := mem_iUnion.mp hxcap
        obtain ⟨hi, z, hz, hzj⟩ := mem_iUnion.mp hxcap
        have hzx : z = x := hj hzj
        subst z
        have hxseam : j x ∈ j '' (D i \ U i) := by
          refine ⟨x, ⟨hz, ?_⟩, rfl⟩
          intro hxU
          exact hx.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxU⟩⟩)
        rw [← hinter i hi] at hxseam
        exact hxseam.1
  rw [heq]
  exact ⟨rfl, hc.image_of_continuousOn (hjcontinuous.mono sdiff_subset),
    hn.image j (hjcontinuous.mono sdiff_subset)⟩

end PoincareConjecture.M25.Topology3D
