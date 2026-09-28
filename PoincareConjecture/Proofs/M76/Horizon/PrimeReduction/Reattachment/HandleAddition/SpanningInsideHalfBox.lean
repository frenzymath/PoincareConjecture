import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductRescaling
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcSignedRegion



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Minus" => Set.prod Square (Icc (-1 : ℝ) 0)

private theorem exists_second_coordinate_disk_rim_chart {z : V2} (hz : z ∈ Rim) :
    ∃ H : OpenPartialHomeomorph V2 P2,
      z ∈ H.source ∧ H z = 0 ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ y ∈ H.source,y ∈ Disk ↔ 0 ≤ (H y).2) ∧
      ∀ y ∈ H.source,y ∈ Rim ↔ (H y).2 = 0 := by
  obtain ⟨H,B,hzH,hHz,hB,_,hHi,hhalf,hrim⟩ := exists_centered_disk_rim_chart hz
  have hne : ∃ v : V2,B v ≠ 0 := by
    by_contra h
    apply hB
    apply LinearMap.ext
    intro v
    exact not_not.mp ((not_exists.mp h) v)
  obtain ⟨v,hv⟩ := hne
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let m := B.toContinuousLinearMap.comp a.symm.toContinuousLinearMap
  let w := a ((B v)⁻¹ • v)
  have hw : m w = 1 := by
    change B (a.symm (a ((B v)⁻¹ • v))) = 1
    rw [a.symm_apply_apply,map_smul]
    exact inv_mul_cancel₀ hv
  obtain ⟨L,hL⟩ := exists_linear_second_coordinate m w hw
  let A := a.trans L
  let Q := H.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hQs : Q.source = H.source := by
    change H.source ∩ H ⁻¹' univ = H.source
    rw [preimage_univ,inter_univ]
  have hval (y : V2) : (Q y).2 = B (H y) := by
    change (L (a (H y))).2 = B (H y)
    rw [hL]
    change B (a.symm (a (H y))) = B (H y)
    rw [a.symm_apply_apply]
  refine ⟨Q,hQs.symm.subset hzH,?_,?_,?_,?_⟩
  · change A (H z) = 0
    rw [hHz,map_zero]
  · exact hHi.comp (locallyPiecewiseAffineOn_affine
      A.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ)
  · intro y hy
    rw [hval]
    exact hhalf y (hQs.subset hy)
  · intro y hy
    rw [hval]
    exact hrim y (hQs.subset hy)




theorem OriginalDiskProduct.exists_inside_half_box_at_half_height_with_image
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N F S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j)
    (hfront : frontier N = N ∩ (F ∪ S)) (hS : IsClosed S)
    {z : V2} (hz : z ∈ Rim) (positive : Bool)
    (hclear : P.map (z,if positive then (1/2 : ℝ) else -1/2) ∉ S) :
    ∃ (H : OpenPartialHomeomorph V2 P2) (ε : ℝ) (u : C3 → X),
      0 < ε ∧ ε ≤ 1/4 ∧ z ∈ H.source ∧ H z = 0 ∧
      PolyhedralPLInCharts e u Minus ∧ InjOn u Minus ∧
      (∀ q ∈ Minus,u q = P.map (H.symm (ε*q.1.2,-ε*q.2),
        if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1))) ∧
      u 0 = P.map (z,if positive then (1/2 : ℝ) else -1/2) ∧
      u '' Minus ⊆ N \ S ∧
      (∀ q ∈ Minus,u q ∈ F ↔ q.2 = 0) ∧
      (∀ q ∈ Minus,u q ∈ P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ q.1.1 ≤ 0) ∧
      u '' Minus ⊆ P.map '' (Disk ×ˢ I) := by
  obtain ⟨H,hzH,hHz,hHi,hhalf,hrim⟩ := exists_second_coordinate_disk_rim_chart hz
  let c : ℝ := if positive then 1/2 else -1/2
  have hc : c ∈ I := by dsimp [c]; split <;> norm_num
  have hzD : z ∈ Disk := sphere_subset_closedBall hz
  have hH0 : H.symm 0 = z := by rw [←hHz,H.left_inv hzH]
  let W : Set (Disk ×ˢ I : Set (V2 × ℝ)) := (fun q => P.map q) ⁻¹' Sᶜ
  have hW : IsOpen W := hS.isOpen_compl.preimage P.polyhedral.continuousOn.domRestrict
  obtain ⟨O,hO,hOW⟩ := isOpen_induced_iff.mp hW
  have hzO : (z,c) ∈ O := by
    change (⟨(z,c),⟨hzD,hc⟩⟩ : Disk ×ˢ I) ∈ (Subtype.val : (Disk ×ˢ I : Set (V2 × ℝ)) → V2 × ℝ) ⁻¹' O
    rw [hOW]
    exact hclear
  let G : C3 → V2 × ℝ := fun q => (H.symm (q.1.2,-q.2),
    if positive then 1/2+q.1.1 else -(1/2+q.1.1))
  let V : Set C3 := {q | (q.1.2,-q.2) ∈ H.target}
  have hV : IsOpen V := H.open_target.preimage (continuous_fst.snd.prodMk continuous_snd.neg)
  have hG : LocallyPiecewiseAffineOn G V := by
    have ha := locallyPiecewiseAffineOn_affine
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap.prod
        (-(ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap)) isOpen_univ
    have hbase : LocallyPiecewiseAffineOn (fun q : C3 => H.symm (q.1.2,-q.2)) V := by
      have hh := hHi.comp ha
      change LocallyPiecewiseAffineOn (fun q : C3 => H.symm (q.1.2,-q.2)) (univ ∩ V) at hh
      simpa only [univ_inter] using hh
    have ht : LocallyPiecewiseAffineOn (fun q : C3 => if positive then 1/2+q.1.1 else -(1/2+q.1.1)) V := by
      let t : C3 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ C3 (1/2 : ℝ) +
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap
      split
      · exact locallyPiecewiseAffineOn_affine t hV
      · exact locallyPiecewiseAffineOn_affine (-t) hV
    exact hbase.prod_mk ht
  have h0V : (0 : C3) ∈ V := by
    change ((0 : ℝ),-(0 : ℝ)) ∈ H.target
    rw [neg_zero]
    change (0 : P2) ∈ H.target
    rw [←hHz]
    exact H.map_source hzH
  have hG0 : G 0 = (z,c) := by
    apply Prod.ext
    · change H.symm ((0 : ℝ),-(0 : ℝ)) = z
      rw [neg_zero]
      exact hH0
    · change (if positive then 1/2+(0 : ℝ) else -(1/2+(0 : ℝ))) = c
      dsimp [c]
      split <;> ring
  have hVO : IsOpen (V ∩ G ⁻¹' O) := hG.continuousOn.isOpen_inter_preimage hV hO
  have h0VO : (0 : C3) ∈ V ∩ G ⁻¹' O := ⟨h0V,by rw [mem_preimage,hG0]; exact hzO⟩
  obtain ⟨δ,hδ,hδV⟩ := CoordinateHalfBoxes.exists_box_subset hVO h0VO
  let ε := min δ (1/4 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεsmall : ε ≤ 1/4 := min_le_right _ _
  let scale : C3 →L[ℝ] C3 := ε • ContinuousLinearMap.id ℝ C3
  have hscale (q : C3) (hq : q ∈ Minus) : scale q ∈ CoordinateHalfBoxes.box δ := by
    change ((-δ ≤ ε*q.1.1 ∧ ε*q.1.1 ≤ δ) ∧ (-δ ≤ ε*q.1.2 ∧ ε*q.1.2 ≤ δ)) ∧
      (-δ ≤ ε*q.2 ∧ ε*q.2 ≤ δ)
    rcases hq with ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨he,hf⟩⟩
    constructor
    · constructor <;> constructor <;> nlinarith
    · constructor <;> nlinarith
  let g : C3 → V2 × ℝ := G ∘ scale
  have hgV (q : C3) (hq : q ∈ Minus) : scale q ∈ V ∩ G ⁻¹' O := hδV (hscale q hq)
  have hgDom (q : C3) (hq : q ∈ Minus) : g q ∈ Disk ×ˢ I := by
    have ht := (hgV q hq).1
    have hb := H.map_target ht
    refine ⟨(hhalf _ hb).mpr ?_,?_⟩
    · rw [H.right_inv ht]
      change 0 ≤ -(ε*q.2)
      nlinarith [hq.2.2]
    · change -1 ≤ (if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1)) ∧
        (if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1)) ≤ 1
      split <;> constructor <;> nlinarith [hq.1.1.1,hq.1.1.2]
  have hgO (q : C3) (hq : q ∈ Minus) : g q ∈ O := (hgV q hq).2
  have hgPL : FinitePiecewiseAffineOn g Minus := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
      ((isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
        (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))).prod
        (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 0))
    change K.space = Minus at hKs
    have hlocal := hG.comp (locallyPiecewiseAffineOn_affine scale.toContinuousAffineMap isOpen_univ)
    have hsub : K.space ⊆ univ ∩ scale ⁻¹' V := fun q hq => ⟨mem_univ _,(hgV q (hKs.subset hq)).1⟩
    rw [←hKs]
    exact hlocal.finitePiecewiseAffineOn K hK hsub
  have hgI : InjOn g Minus := by
    intro q hq w hw heq
    have hbase := congrArg Prod.fst heq
    have ht := congrArg Prod.snd heq
    have hh := H.symm.injOn (hgV q hq).1 (hgV w hw).1 hbase
    have hq2 : q.2 = w.2 := by
      have h := congrArg Prod.snd hh
      change -(ε*q.2) = -(ε*w.2) at h
      nlinarith
    have hq12 : q.1.2 = w.1.2 := by
      have h := congrArg Prod.fst hh
      change ε*q.1.2 = ε*w.1.2 at h
      nlinarith
    have hq11 : q.1.1 = w.1.1 := by
      change (if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1)) =
        (if positive then 1/2+ε*w.1.1 else -(1/2+ε*w.1.1)) at ht
      split at ht <;> nlinarith
    exact Prod.ext (Prod.ext hq11 hq12) hq2
  let u := P.map ∘ g
  have hu : PolyhedralPLInCharts e u Minus := by
    obtain ⟨K,hK,hKs,hKf⟩ := hgPL
    rw [←hKs]
    exact P.polyhedral.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩
      (fun q hq => hgDom q (hKs.subset hq))
  have hui : InjOn u Minus := fun q hq w hw hqw => hgI hq hw (P.injective (hgDom q hq) (hgDom w hw) hqw)
  have huNS (q : C3) (hq : q ∈ Minus) : u q ∈ N \ S := by
    refine ⟨P.inside (hgDom q hq),?_⟩
    have hh : (⟨g q,hgDom q hq⟩ : Disk ×ˢ I) ∈ W := by rw [←hOW]; exact hgO q hq
    exact hh
  refine ⟨H,ε,u,hε,hεsmall,hzH,hHz,hu,hui,?_,?_,?_,?_,?_,?_⟩
  · intro q hq
    change P.map (H.symm (ε*q.1.2,-(ε*q.2)),_) = _
    rw [neg_mul]
    rfl
  · change P.map (G (scale 0)) = _
    rw [map_zero,hG0]
  · rintro _ ⟨q,hq,rfl⟩
    exact huNS q hq
  · intro q hq
    have hf : u q ∈ F ↔ u q ∈ frontier N := by rw [hfront]; exact ⟨fun h => ⟨(huNS q hq).1,Or.inl h⟩,fun h => h.2.resolve_right (huNS q hq).2⟩
    rw [hf]
    change P.map (g q) ∈ frontier N ↔ q.2 = 0
    rw [P.proper (g q) (hgDom q hq)]
    change H.symm ((scale q).1.2,-(scale q).2) ∈ Rim ↔ q.2 = 0
    rw [hrim _ (H.map_target (hgV q hq).1),H.right_inv (hgV q hq).1]
    change -(ε*q.2) = 0 ↔ q.2 = 0
    constructor <;> intro h
    · nlinarith
    · rw [h,mul_zero,neg_zero]
  · intro q hq
    have hm : u q ∈ P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ (g q).2 ∈ Icc (-1/2 : ℝ) (1/2) := by
      constructor
      · rintro ⟨w,hw,heq⟩
        have hwI : w ∈ Disk ×ˢ I := ⟨hw.1,by constructor <;> linarith [hw.2.1,hw.2.2]⟩
        have h := P.injective hwI (hgDom q hq) heq
        exact h ▸ hw.2
      · exact fun h => ⟨g q,⟨(hgDom q hq).1,h⟩,rfl⟩
    rw [hm]
    change ((-1/2 : ℝ) ≤ (if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1)) ∧
      (if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1)) ≤ 1/2) ↔ q.1.1 ≤ 0
    split <;> constructor <;> intro h
    · nlinarith [h.2]
    · constructor <;> nlinarith [hq.1.1.1]
    · nlinarith [h.1]
    · constructor <;> nlinarith [hq.1.1.1]

  · rintro _ ⟨q,hq,rfl⟩
    exact ⟨g q,hgDom q hq,rfl⟩

theorem OriginalDiskProduct.exists_inside_half_box_at_half_height
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N F S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j)
    (hfront : frontier N = N ∩ (F ∪ S)) (hS : IsClosed S)
    {z : V2} (hz : z ∈ Rim) (positive : Bool)
    (hclear : P.map (z,if positive then (1/2 : ℝ) else -1/2) ∉ S) :
    ∃ (H : OpenPartialHomeomorph V2 P2) (ε : ℝ) (u : C3 → X),
      0 < ε ∧ ε ≤ 1/4 ∧ z ∈ H.source ∧ H z = 0 ∧
      PolyhedralPLInCharts e u Minus ∧ InjOn u Minus ∧
      (∀ q ∈ Minus,u q = P.map (H.symm (ε*q.1.2,-ε*q.2),
        if positive then 1/2+ε*q.1.1 else -(1/2+ε*q.1.1))) ∧
      u 0 = P.map (z,if positive then (1/2 : ℝ) else -1/2) ∧
      u '' Minus ⊆ N \ S ∧
      (∀ q ∈ Minus,u q ∈ F ↔ q.2 = 0) ∧
      ∀ q ∈ Minus,u q ∈ P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ q.1.1 ≤ 0 := by
  obtain ⟨H,ε,u,hε,hεsmall,hzH,hHz,hu,hui,huval,hu0,huNS,huF,huQ,_⟩ :=
    P.exists_inside_half_box_at_half_height_with_image hfront hS hz positive hclear
  exact ⟨H,ε,u,hε,hεsmall,hzH,hHz,hu,hui,huval,hu0,huNS,huF,huQ⟩

end PoincareConjecture.M76
