import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ConvexFrontierSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ClosedJordanSide

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

private theorem zero_mem_closure_convex_strict_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Set E} (hV : Convex ℝ V) (ell : E →L[ℝ] ℝ)
    {x y : E} (hx : x ∈ V) (hy : y ∈ V) (hx0 : ell x = 0) (hypos : 0 < ell y) :
    x ∈ closure (V ∩ ell ⁻¹' Ioi 0) := by
  have hseg : openSegment ℝ x y ⊆ V ∩ ell ⁻¹' Ioi 0 := by
    rintro z ⟨a,b,ha,hb,hab,rfl⟩
    refine ⟨hV hx hy ha.le hb.le hab,?_⟩
    change 0 < ell (a • x + b • y)
    rw [map_add,map_smul,map_smul,hx0,smul_zero,zero_add]
    exact mul_pos hb hypos
  exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

theorem frontier_closure_local_of_convex_flat_frontier
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set X} (hO : IsOpen O) (H : OpenPartialHomeomorph X E)
    (ell : E →L[ℝ] ℝ) (hcv : Convex ℝ H.target)
    (hfront : ∀ x ∈ H.source, x ∈ frontier O ↔ ell (H x) = 0)
    {p : X} (hp : p ∈ frontier (closure O)) (hpH : p ∈ H.source) :
    ∀ x ∈ H.source, x ∈ frontier O → x ∈ frontier (closure O) := by
  let P := H.symm '' (H.target ∩ ell ⁻¹' Ioi 0)
  let N := H.symm '' (H.target ∩ ell ⁻¹' Iio 0)
  have hP : IsPreconnected P :=
    (hcv.inter ((convex_Ioi (0 : ℝ)).linear_preimage ell.toLinearMap)).isPreconnected.image
      H.symm (H.continuousOn_symm.mono inter_subset_left)
  have hN : IsPreconnected N :=
    (hcv.inter ((convex_Iio (0 : ℝ)).linear_preimage ell.toLinearMap)).isPreconnected.image
      H.symm (H.continuousOn_symm.mono inter_subset_left)
  have hPm (x : X) (hx : x ∈ H.source) : x ∈ P ↔ 0 < ell (H x) := by
    constructor
    · rintro ⟨y,hy,rfl⟩; rw [H.right_inv hy.1]; exact hy.2
    · intro ht; exact ⟨H x,⟨H.map_source hx,ht⟩,H.left_inv hx⟩
  have hNm (x : X) (hx : x ∈ H.source) : x ∈ N ↔ ell (H x) < 0 := by
    constructor
    · rintro ⟨y,hy,rfl⟩; rw [H.right_inv hy.1]; exact hy.2
    · intro ht; exact ⟨H x,⟨H.map_source hx,ht⟩,H.left_inv hx⟩
  have hPdis : Disjoint (frontier O) P := by
    apply disjoint_left.mpr
    rintro x hx ⟨y,hy,rfl⟩
    have hh := (hfront _ (H.map_target hy.1)).mp hx
    rw [H.right_inv hy.1] at hh
    exact (ne_of_gt hy.2) hh
  have hNdis : Disjoint (frontier O) N := by
    apply disjoint_left.mpr
    rintro x hx ⟨y,hy,rfl⟩
    have hh := (hfront _ (H.map_target hy.1)).mp hx
    rw [H.right_inv hy.1] at hh
    exact (ne_of_lt hy.2) hh
  have hpO : p ∈ closure O := by simpa only [closure_closure] using hp.1
  have hpout : p ∈ closure (closure O)ᶜ := by
    rw [closure_compl]
    exact hp.2
  obtain ⟨a,haH,haO⟩ := mem_closure_iff.mp hpO H.source H.open_source hpH
  obtain ⟨b,hbH,hbout⟩ := mem_closure_iff.mp hpout H.source H.open_source hpH
  have hane : ell (H a) ≠ 0 := fun hh =>
    ((hfront a haH).mpr hh).2 (hO.interior_eq.symm ▸ haO)
  have hbne : ell (H b) ≠ 0 := fun hh => hbout (frontier_subset_closure ((hfront b hbH).mpr hh))
  have hout {T : Set X} (hc : IsPreconnected T) (hd : Disjoint (frontier O) T)
      (hb : b ∈ T) : T ⊆ (closure O)ᶜ := by
    apply hc.m76_subset_of_disjoint_frontier isClosed_closure.isOpen_compl ?_ ⟨b,hb,hbout⟩
    rw [frontier_compl]
    exact hd.mono_left frontier_closure_subset
  have hlabel : (P ⊆ O ∧ N ⊆ (closure O)ᶜ) ∨ (N ⊆ O ∧ P ⊆ (closure O)ᶜ) := by
    rcases lt_or_gt_of_ne hane with ha | ha
    · have hNO := hN.m76_subset_of_disjoint_frontier hO hNdis ⟨a,(hNm a haH).mpr ha,haO⟩
      have hbpos : 0 < ell (H b) := lt_of_le_of_ne (by
        by_contra hh
        exact hbout (subset_closure (hNO ((hNm b hbH).mpr (lt_of_not_ge hh))))) (Ne.symm hbne)
      exact Or.inr ⟨hNO,hout hP hPdis ((hPm b hbH).mpr hbpos)⟩
    · have hPO := hP.m76_subset_of_disjoint_frontier hO hPdis ⟨a,(hPm a haH).mpr ha,haO⟩
      have hbneg : ell (H b) < 0 := lt_of_le_of_ne (by
        by_contra hh
        exact hbout (subset_closure (hPO ((hPm b hbH).mpr (lt_of_not_ge hh))))) hbne
      exact Or.inl ⟨hPO,hout hN hNdis ((hNm b hbH).mpr hbneg)⟩
  have hPne : P.Nonempty := by
    rcases lt_or_gt_of_ne hane with ha | ha
    · rcases lt_or_gt_of_ne hbne with hb | hb
      · exact False.elim (hbout (subset_closure
          (hN.m76_subset_of_disjoint_frontier hO hNdis ⟨a,(hNm a haH).mpr ha,haO⟩
            ((hNm b hbH).mpr hb))))
      · exact ⟨b,(hPm b hbH).mpr hb⟩
    · exact ⟨a,(hPm a haH).mpr ha⟩
  have hNne : N.Nonempty := by
    rcases lt_or_gt_of_ne hane with ha | ha
    · exact ⟨a,(hNm a haH).mpr ha⟩
    · rcases lt_or_gt_of_ne hbne with hb | hb
      · exact ⟨b,(hNm b hbH).mpr hb⟩
      · exact False.elim (hbout (subset_closure
          (hP.m76_subset_of_disjoint_frontier hO hPdis ⟨a,(hPm a haH).mpr ha,haO⟩
            ((hPm b hbH).mpr hb))))
  intro x hx hf
  have hx0 := (hfront x hx).mp hf
  have hxP : x ∈ closure P := by
    obtain ⟨_,y,hy,rfl⟩ := hPne
    have hh := zero_mem_closure_convex_strict_side hcv ell (H.map_source hx) hy.1 hx0 hy.2
    have hh' := mem_closure_image
      (H.continuousOn_symm.continuousAt (H.open_target.mem_nhds (H.map_source hx))) hh
    simpa only [H.left_inv hx] using hh'
  have hxN : x ∈ closure N := by
    obtain ⟨_,y,hy,rfl⟩ := hNne
    have hh := zero_mem_closure_convex_strict_side hcv (-ell) (H.map_source hx) hy.1
      (by simpa using hx0) (by exact neg_pos.mpr (show ell y < 0 from hy.2))
    have hh' := mem_closure_image
      (H.continuousOn_symm.continuousAt (H.open_target.mem_nhds (H.map_source hx))) hh
    have heq : H.target ∩ (-ell) ⁻¹' Ioi 0 = H.target ∩ ell ⁻¹' Iio 0 := by
      ext z
      simp
    rw [heq] at hh'
    simpa only [H.left_inv hx] using hh'
  rcases hlabel with h | h
  · exact ⟨subset_closure (closure_mono h.1 hxP),by
      have hh := closure_mono h.2 hxN
      rwa [closure_compl] at hh⟩
  · exact ⟨subset_closure (closure_mono h.1 hxN),by
      have hh := closure_mono h.2 hxP
      rwa [closure_compl] at hh⟩

theorem frontier_closure_eq_of_connected_flat_frontier
    {X E : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set X} (hO : IsOpen O) (hne : O.Nonempty) (hproper : closure O ≠ univ)
    (hconn : IsConnected (frontier O))
    (hcharts : ∀ x ∈ frontier O, ∃ H : OpenPartialHomeomorph X E,
      x ∈ H.source ∧ ∃ ell : E →L[ℝ] ℝ, Convex ℝ H.target ∧
        ∀ y ∈ H.source, y ∈ frontier O ↔ ell (H y) = 0) :
    frontier (closure O) = frontier O := by
  let : ConnectedSpace (frontier O) := isConnected_iff_connectedSpace.mp hconn
  let F : Set (frontier O) := Subtype.val ⁻¹' frontier (closure O)
  have hFc : IsClosed F := isClosed_frontier.preimage continuous_subtype_val
  have hFo : IsOpen F := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨H,hxH,ell,hcv,hfront⟩ := hcharts x x.property
    have hopen : IsOpen ((Subtype.val : frontier O → X) ⁻¹' H.source) :=
      H.open_source.preimage continuous_subtype_val
    apply Filter.mem_of_superset (hopen.mem_nhds hxH)
    intro y hy
    exact frontier_closure_local_of_convex_flat_frontier hO H ell hcv hfront hx hxH y hy y.property
  have hFn : F.Nonempty := by
    obtain ⟨x,hx⟩ := nonempty_frontier_iff.mpr ⟨hne.mono subset_closure,hproper⟩
    exact ⟨⟨x,frontier_closure_subset hx⟩,hx⟩
  have hFu : F = univ := (isClopen_iff.mp ⟨hFc,hFo⟩).resolve_left hFn.ne_empty
  apply Subset.antisymm frontier_closure_subset
  intro x hx
  exact hFu.symm.subset (mem_univ (⟨x,hx⟩ : frontier O))

end PoincareConjecture.M76
