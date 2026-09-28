import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks
import Mathlib.SetTheory.Cardinal.NatCard








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private theorem clopen_of_open_partition
    {X ι : Type*} [TopologicalSpace X] {U : ι → Set X}
    (hopen : ∀ i, IsOpen (U i)) (hdisj : Pairwise (Disjoint on U))
    (hcover : ⋃ i, U i = univ) (i : ι) : IsClopen (U i) := by
  refine ⟨?_, hopen i⟩
  rw [← isOpen_compl_iff]
  have heq : (U i)ᶜ = ⋃ j : {j : ι // j ≠ i}, U j.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover x
      have hji : j ≠ i := by rintro rfl; exact hx hj
      exact mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hx hi
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact disjoint_left.mp (hdisj j.property) hj hi
  rw [heq]
  exact isOpen_iUnion fun j => hopen j.val

private theorem component_equiv_of_three_open_pieces
    {X : Type*} [TopologicalSpace X] (p : X) {U V : Set X}
    (hC : IsOpen (connectedComponent p)) (hU : IsOpen U) (hV : IsOpen V)
    (hCU : Disjoint (connectedComponent p) U) (hCV : Disjoint (connectedComponent p) V)
    (hUV : Disjoint U V) (hcover : connectedComponent p ∪ U ∪ V = univ) :
    IsClopen U ∧ IsClopen V ∧
      (∀ x, x ∉ connectedComponent p →
        Xor (connectedComponent x ⊆ U) (connectedComponent x ⊆ V)) ∧
      ∃ E : ConnectedComponents X ≃ Option (ConnectedComponents U ⊕ ConnectedComponents V),
        E (ConnectedComponents.mk p) = none ∧
        (∀ x : U, E (ConnectedComponents.mk x.val) =
          some (Sum.inl (ConnectedComponents.mk x))) ∧
        ∀ x : V, E (ConnectedComponents.mk x.val) =
          some (Sum.inr (ConnectedComponents.mk x)) := by
  let W : Option Bool → Set X
    | none => connectedComponent p
    | some false => U
    | some true => V
  have hWopen (i : Option Bool) : IsOpen (W i) := by
    rcases i with _ | (_ | _) <;> assumption
  have hWdisj : Pairwise (Disjoint on W) := by
    intro i j hij
    rcases i with _ | (_ | _) <;> rcases j with _ | (_ | _)
      <;> try exact (hij rfl).elim
    all_goals
      first
      | exact hCU
      | exact hCU.symm
      | exact hCV
      | exact hCV.symm
      | exact hUV
      | exact hUV.symm
  have hWcover : ⋃ i, W i = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    rcases hcover.symm ▸ mem_univ x with (hc | hu) | hv
    · exact ⟨none, hc⟩
    · exact ⟨some false, hu⟩
    · exact ⟨some true, hv⟩
  have hWclopen := clopen_of_open_partition hWopen hWdisj hWcover
  have hUc : IsClopen U := hWclopen (some false)
  have hVc : IsClopen V := hWclopen (some true)
  let : ConnectedSpace (W none) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : Unique (ConnectedComponents (W none)) := (nonempty_unique _).some
  let Q : (Σ i, ConnectedComponents (W i)) ≃
      Option (ConnectedComponents U ⊕ ConnectedComponents V) := {
    toFun := fun z => match z with
      | ⟨none, _⟩ => none
      | ⟨some false, y⟩ => some (Sum.inl y)
      | ⟨some true, y⟩ => some (Sum.inr y)
    invFun := fun z => match z with
      | none => ⟨none, default⟩
      | some (Sum.inl y) => ⟨some false, y⟩
      | some (Sum.inr y) => ⟨some true, y⟩
    left_inv := by
      rintro ⟨i, y⟩
      rcases i with _ | (_ | _)
      · exact congrArg (fun z : ConnectedComponents (W none) =>
          (⟨none, z⟩ : Σ i, ConnectedComponents (W i)))
          (Subsingleton.elim _ _)
      · rfl
      · rfl
    right_inv := by rintro (_ | (y | y)) <;> rfl }
  let E := (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover).trans Q
  refine ⟨hUc, hVc, ?_, E, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : x ∈ U ∨ x ∈ V := by
      have := hcover.symm ▸ mem_univ x
      rcases this with (hc | hu) | hv
      · exact (hx hc).elim
      · exact Or.inl hu
      · exact Or.inr hv
    have hnot (hxu : connectedComponent x ⊆ U) (hxv : connectedComponent x ⊆ V) : False :=
      disjoint_left.mp hUV (hxu mem_connectedComponent) (hxv mem_connectedComponent)
    rcases hmem with hxu | hxv
    · exact Or.inl ⟨hUc.connectedComponent_subset hxu, fun hxv =>
        hnot (hUc.connectedComponent_subset hxu) hxv⟩
    · exact Or.inr ⟨hVc.connectedComponent_subset hxv, fun hxu =>
        hnot hxu (hVc.connectedComponent_subset hxv)⟩
  · change Q (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover
      (ConnectedComponents.mk p)) = none
    rw [ConnectedComponents.equivOfIsClopen_mk (i := none) hWclopen hWdisj hWcover p
      (show p ∈ W none from mem_connectedComponent)]
    rfl
  · intro x
    change Q (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover
      (ConnectedComponents.mk x.val)) = _
    rw [ConnectedComponents.equivOfIsClopen_mk (i := some false) hWclopen hWdisj hWcover x.val
      (show x.val ∈ W (some false) from x.property)]
    rfl
  · intro x
    change Q (ConnectedComponents.equivOfIsClopen hWclopen hWdisj hWcover
      (ConnectedComponents.mk x.val)) = _
    rw [ConnectedComponents.equivOfIsClopen_mk (i := some true) hWclopen hWdisj hWcover x.val
      (show x.val ∈ W (some true) from x.property)]
    rfl






theorem level_components_of_parallel_disks
    {h : S2 → Real} {c ε a : Real} (ha : 0 < a) (haε : a < ε)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (hheight : ∀ q t, t ∈ Ioo (-ε) ε → h (T (q, t)) = c + t)
    (p : S2) (hp : h p = c)
    (hcenter : range (fun q : S1 => T (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p)
    (eMinus ePlus : OpenPartialHomeomorph E2 S2)
    (hsMinus : closedBall 0 1 ⊆ eMinus.source) (hsPlus : closedBall 0 1 ⊆ ePlus.source)
    (hdisjoint : Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1))
    (hslab : T '' (univ ×ˢ Icc (-a) a) =
      (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ) :
    let L := h ⁻¹' {c}
    let Lminus : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
    let Lplus : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
    L \ connectedComponentIn L p =
      (L ∩ eMinus '' ball 0 1) ∪ (L ∩ ePlus '' ball 0 1) ∧
      IsClopen Lminus ∧ IsClopen Lplus ∧
      (∀ x : L, x ∉ connectedComponent (⟨p, hp⟩ : L) →
        Xor (connectedComponent x ⊆ Lminus) (connectedComponent x ⊆ Lplus)) ∧
      ∃ E : ConnectedComponents L ≃
          Option (ConnectedComponents Lminus ⊕ ConnectedComponents Lplus),
        E (ConnectedComponents.mk (⟨p, hp⟩ : L)) = none ∧
        (∀ x : Lminus, E (ConnectedComponents.mk x.val) =
          some (Sum.inl (ConnectedComponents.mk x))) ∧
        ∀ x : Lplus, E (ConnectedComponents.mk x.val) =
          some (Sum.inr (ConnectedComponents.mk x)) := by
  let L := h ⁻¹' {c}
  let pL : L := ⟨p, hp⟩
  let U : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
  let V : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
  have hε : 0 < ε := ha.trans haε
  have hzero : (0 : Real) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hC : (Subtype.val : L → S2) ⁻¹' range (fun q : S1 => T (q, 0)) =
      connectedComponent pL := by
    rw [hcenter, connectedComponentIn_eq_image (show p ∈ h ⁻¹' {c} from hp),
      preimage_image_eq _ Subtype.val_injective]
  have hCmem (x : L) : x ∈ connectedComponent pL ↔
      x.val ∈ connectedComponentIn L p := by
    rw [← hC, hcenter]
    rfl
  have htarget : (Subtype.val : L → S2) ⁻¹' range (fun q : S1 => T (q, 0)) =
      Subtype.val ⁻¹' T.target := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      change x.val ∈ T.target
      rw [← hq]
      exact T.map_source (hsource ▸ ⟨mem_univ _, hzero⟩)
    · intro hx
      have hz := T.map_target hx
      rw [hsource] at hz
      have ht : (T.symm x.val).2 = 0 := by
        have heq := hheight (T.symm x.val).1 (T.symm x.val).2 hz.2
        change h (T (T.symm x.val)) = c + (T.symm x.val).2 at heq
        rw [T.right_inv hx] at heq
        have hxlevel : h x.val = c := x.property
        linarith
      refine ⟨(T.symm x.val).1, ?_⟩
      have heq : ((T.symm x.val).1, 0) = T.symm x.val := Prod.ext rfl ht.symm
      change T ((T.symm x.val).1, 0) = x.val
      rw [heq, T.right_inv hx]
  have hCopen : IsOpen (connectedComponent pL) := by
    rw [← hC, htarget]
    exact T.open_target.preimage continuous_subtype_val
  have hU : IsOpen U :=
    (eMinus.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsMinus)).preimage
      continuous_subtype_val
  have hV : IsOpen V :=
    (ePlus.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsPlus)).preimage
      continuous_subtype_val
  have hslablevel (x : L) : x.val ∈ T '' (univ ×ˢ Icc (-a) a) ↔
      x ∈ connectedComponent pL := by
    rw [← hC]
    constructor
    · rintro ⟨⟨q, t⟩, ht, hTx⟩
      have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
      have heq := hheight q t htε
      rw [hTx] at heq
      have hxlevel : h x.val = c := x.property
      have ht0 : t = 0 := by linarith
      exact ⟨q, ht0 ▸ hTx⟩
    · rintro ⟨q, hq⟩
      exact ⟨(q, 0), ⟨mem_univ _, ⟨by linarith, ha.le⟩⟩, hq⟩
  have hCU : Disjoint (connectedComponent pL) U := by
    apply disjoint_left.mpr
    intro x hx hu
    have hs := (hslablevel x).mpr hx
    rw [hslab] at hs
    exact hs (Or.inl hu)
  have hCV : Disjoint (connectedComponent pL) V := by
    apply disjoint_left.mpr
    intro x hx hv
    have hs := (hslablevel x).mpr hx
    rw [hslab] at hs
    exact hs (Or.inr hv)
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hdisjoint
      (image_mono ball_subset_closedBall hx) (image_mono ball_subset_closedBall hy)
  have hcover : connectedComponent pL ∪ U ∪ V = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ connectedComponent pL
    · exact Or.inl (Or.inl hx)
    · have hnot : x.val ∉ T '' (univ ×ˢ Icc (-a) a) := fun hs => hx ((hslablevel x).mp hs)
      rw [hslab] at hnot
      rcases not_not.mp hnot with hu | hv
      · exact Or.inl (Or.inr hu)
      · exact Or.inr hv
  refine ⟨?_, component_equiv_of_three_open_pieces pL hCopen hU hV hCU hCV hUV hcover⟩
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    have hc : (⟨x, hx⟩ : L) ∈ connectedComponent pL ∪ U ∪ V := hcover.symm ▸ mem_univ _
    rcases hc with (hc | hu) | hv
    · exact (hxc ((hCmem ⟨x, hx⟩).mp hc)).elim
    · exact Or.inl ⟨hx, hu⟩
    · exact Or.inr ⟨hx, hv⟩
  · rintro (⟨hx, hu⟩ | ⟨hx, hv⟩)
    · exact ⟨hx, fun hc => disjoint_left.mp hCU ((hCmem ⟨x, hx⟩).mpr hc) hu⟩
    · exact ⟨hx, fun hc => disjoint_left.mp hCV ((hCmem ⟨x, hx⟩).mpr hc) hv⟩



theorem card_level_components_of_parallel_disks
    {h : S2 → Real} {c ε a : Real} (ha : 0 < a) (haε : a < ε)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (hheight : ∀ q t, t ∈ Ioo (-ε) ε → h (T (q, t)) = c + t)
    (p : S2) (hp : h p = c)
    (hcenter : range (fun q : S1 => T (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p)
    (eMinus ePlus : OpenPartialHomeomorph E2 S2)
    (hsMinus : closedBall 0 1 ⊆ eMinus.source) (hsPlus : closedBall 0 1 ⊆ ePlus.source)
    (hdisjoint : Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1))
    (hslab : T '' (univ ×ˢ Icc (-a) a) =
      (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ)
    [Finite (ConnectedComponents (h ⁻¹' {c}))] :
    let L := h ⁻¹' {c}
    let Lminus : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
    let Lplus : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
    Finite (ConnectedComponents Lminus) ∧ Finite (ConnectedComponents Lplus) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) + 1 =
        Nat.card (ConnectedComponents L) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) <
        Nat.card (ConnectedComponents L) := by
  let L := h ⁻¹' {c}
  let U : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
  let V : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
  obtain ⟨_, _, _, _, E, _⟩ := level_components_of_parallel_disks ha haε T hsource hheight
    p hp hcenter eMinus ePlus hsMinus hsPlus hdisjoint hslab
  let : Finite (Option (ConnectedComponents U ⊕ ConnectedComponents V)) :=
    Finite.of_equiv (ConnectedComponents L) E
  let : Finite (ConnectedComponents U ⊕ ConnectedComponents V) :=
    Finite.of_injective (fun x : ConnectedComponents U ⊕ ConnectedComponents V => some x)
      (Option.some_injective _)
  let : Finite (ConnectedComponents U) := Finite.of_injective
    (Sum.inl : ConnectedComponents U → ConnectedComponents U ⊕ ConnectedComponents V)
    Sum.inl_injective
  let : Finite (ConnectedComponents V) := Finite.of_injective
    (Sum.inr : ConnectedComponents V → ConnectedComponents U ⊕ ConnectedComponents V)
    Sum.inr_injective
  have heq : Nat.card (ConnectedComponents U) + Nat.card (ConnectedComponents V) + 1 =
      Nat.card (ConnectedComponents L) := by
    simpa only [Finite.card_option, Nat.card_sum] using (Nat.card_congr E).symm
  refine ⟨inferInstance, inferInstance, heq, ?_⟩
  change Nat.card (ConnectedComponents U) + Nat.card (ConnectedComponents V) <
    Nat.card (ConnectedComponents L)
  omega



theorem level_inter_disk_closed_eq_open_of_boundary_ne
    {h : S2 → Real} {c : Real} (e : E2 → S2)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (e x) ≠ c) :
    (h ⁻¹' {c}) ∩ e '' closedBall 0 1 = (h ⁻¹' {c}) ∩ e '' ball 0 1 := by
  apply Subset.antisymm
  · rintro y ⟨hy, x, hx, rfl⟩
    refine ⟨hy, x, ?_, rfl⟩
    have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    apply mem_ball_zero_iff.mpr
    apply lt_of_le_of_ne hxle
    intro heq
    exact hboundary x (mem_sphere_zero_iff_norm.mpr heq) hy
  · exact inter_subset_inter_right _ (image_mono ball_subset_closedBall)

end Poincare.Manifold.Schoenflies
