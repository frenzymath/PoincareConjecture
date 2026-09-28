import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallInteriorChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Box" => Set.prod Square (Icc (-1 : ℝ) 1)
local notation "Minus" => Set.prod Square (Icc (-1 : ℝ) 0)
local notation "Plus" => Set.prod Square (Icc (0 : ℝ) 1)
local notation "Base" => Set.prod Square ({0} : Set ℝ)

theorem exists_original_chart_of_ball_embedding
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d r : Set C3} (hd : IsFinitePLBallPair C3 d r)
    {f : C3 → X} (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    (A : V3 ≃L[ℝ] C3) :
    ∃ Q : OpenPartialHomeomorph X V3,
      Q.source = f '' interior d ∧ Q.target = A ⁻¹' interior d ∧
      (∀ z,Q.symm z = f (A z)) ∧
      (∀ z ∈ interior d,Q (f z) = A.symm z) ∧
      ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  classical
  obtain ⟨b⟩ := exists_chartwisePLBall_image hd A.symm hf subset_rfl hfi
  have hint : interior (f '' d) = f '' interior d := by
    rw [b.interior_eq_sdiff,hd.interior_eq_sdiff_of_finrank_eq rfl,hfi.image_sdiff_subset hd.1]
  let : CompactSpace d := isCompact_iff_compactSpace.mp hd.isCompact
  let G : d ≃ₜ (f '' d) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f d hfi) (hf.continuousOn.domRestrict.subtype_mk _)
  let q : X → C3 := fun x => if hx : x ∈ f '' d then (G.symm ⟨x,hx⟩ : C3) else 0
  have hqval (x : f '' d) : q x = (G.symm x : C3) := by simp only [q,dif_pos x.property]
  have hqmap {x : X} (hx : x ∈ f '' d) : q x ∈ d := by
    rw [hqval ⟨x,hx⟩]
    exact (G.symm ⟨x,hx⟩).property
  have hqf (z : C3) (hz : z ∈ d) : q (f z) = z := by
    rw [hqval ⟨f z,⟨z,hz,rfl⟩⟩]
    exact congrArg Subtype.val (G.symm_apply_apply ⟨z,hz⟩)
  have hfq {x : X} (hx : x ∈ f '' d) : f (q x) = x := by
    rw [hqval ⟨x,hx⟩]
    exact congrArg Subtype.val (G.apply_symm_apply ⟨x,hx⟩)
  have hqc : ContinuousOn q (f '' d) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp G.symm.continuous using 1
    funext x
    exact hqval x
  have hsource {x : X} (hx : x ∈ f '' interior d) : q x ∈ interior d := by
    rcases hx with ⟨z,hz,rfl⟩
    rw [hqf z (interior_subset hz)]
    exact hz
  let Q0 : OpenPartialHomeomorph X C3 := {
    toFun := q
    invFun := f
    source := f '' interior d
    target := interior d
    map_source' := fun _ hx => hsource hx
    map_target' := fun z hz => ⟨z,hz,rfl⟩
    left_inv' := fun _ hx => hfq ((image_mono interior_subset) hx)
    right_inv' := fun z hz => hqf z (interior_subset hz)
    open_source := hint ▸ isOpen_interior
    open_target := isOpen_interior
    continuousOn_toFun := hqc.mono (image_mono interior_subset)
    continuousOn_invFun := hf.continuousOn.mono interior_subset }
  let Q := Q0.trans A.symm.toHomeomorph.toOpenPartialHomeomorph
  have hQs : Q.source = f '' interior d := by
    change (f '' interior d) ∩ q ⁻¹' univ = f '' interior d
    rw [preimage_univ,inter_univ]
  have hQt : Q.target = A ⁻¹' interior d := by
    change univ ∩ A ⁻¹' interior d = A ⁻¹' interior d
    rw [univ_inter]
  refine ⟨Q,hQs,hQt,fun _ => rfl,?_,?_⟩
  · intro z hz
    change A.symm (q (f z)) = A.symm z
    rw [hqf z (interior_subset hz)]
  · intro i
    let T := (e i).symm.trans Q
    have hlocal : LocallyPiecewiseAffineOn (fun z => A (T z)) T.source :=
      hf.locallyPiecewiseAffineOn_inverse_comp hfi (e i) (he i)
        (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) T.open_source)
        (A.continuous.comp_continuousOn T.continuousOn)
        (fun y hy => interior_subset (hQt.subset (Q.map_source hy.2)))
        (fun _ hy => hy.1) (fun y hy => Q.left_inv hy.2)
    have hAi := locallyPiecewiseAffineOn_affine
      A.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    change LocallyPiecewiseAffineOn T T.source
    simpa [Function.comp_def] using hAi.comp hlocal

theorem exists_original_chart_of_glued_half_boxes
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {u v : C3 → X} {E : Set X}
    (hu : PolyhedralPLInCharts e u Minus) (hui : InjOn u Minus)
    (hv : PolyhedralPLInCharts e v Plus) (hvi : InjOn v Plus)
    (huE : u '' Minus ⊆ E)
    (hvE : ∀ z ∈ Plus,v z ∈ E ↔ z.2 = 0)
    (huv : EqOn u v Base) (A : V3 ≃L[ℝ] C3) :
    ∃ (f : C3 → X) (Q : OpenPartialHomeomorph X V3),
      PolyhedralPLInCharts e f Box ∧ InjOn f Box ∧
      EqOn f u Minus ∧ EqOn f v Plus ∧
      Q.source = f '' interior Box ∧ Q.target = A ⁻¹' interior Box ∧
      (∀ z,Q.symm z = f (A z)) ∧
      (∀ z ∈ interior Box,Q (f z) = A.symm z) ∧
      u 0 ∈ Q.source ∧ Q (u 0) = 0 ∧
      ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  have hi := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hm := (hi.prod hi).prod (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 0))
  have hp := (hi.prod hi).prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  have hb := (hi.prod hi).prod hi
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hm
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hp
  change K.space = Minus at hKs
  change L.space = Plus at hLs
  have hmeet : Minus ∩ Plus = Base := by
    ext z
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hm,hp⟩
      exact ⟨hm.1,le_antisymm hm.2.2 hp.2.1⟩
    · intro h
      exact ⟨⟨h.1,by rw [h.2]; norm_num⟩,⟨h.1,by rw [h.2]; norm_num⟩⟩
  obtain ⟨f,hf,hfu,hfv⟩ := _root_.Dehn.exists_circle_attachment_map_union he K L hK hL
    (hKs.symm ▸ hu) (hLs.symm ▸ hv)
    (fun z hz hz' => huv (hmeet.subset ⟨hKs.subset hz,hLs.subset hz'⟩))
  have hparts : Minus ∪ Plus = Box := by
    ext z
    constructor
    · rintro (h | h)
      · exact ⟨h.1,⟨h.2.1,by linarith [h.2.2]⟩⟩
      · exact ⟨h.1,⟨by linarith [h.2.1],h.2.2⟩⟩
    · intro h
      by_cases ht : z.2 ≤ 0
      · exact Or.inl ⟨h.1,⟨h.2.1,ht⟩⟩
      · exact Or.inr ⟨h.1,⟨(lt_of_not_ge ht).le,h.2.2⟩⟩
  have hf' : PolyhedralPLInCharts e f Box := by simpa only [hKs,hLs,hparts] using hf
  have hfu' : EqOn f u Minus := hKs ▸ hfu
  have hfv' : EqOn f v Plus := hLs ▸ hfv
  have hcross (z w : C3) (hz : z ∈ Minus) (hw : w ∈ Plus) (heq : f z = f w) : z = w := by
    have huvzw : u z = v w := (hfu' hz).symm.trans (heq.trans (hfv' hw))
    have hvwE : v w ∈ E := huvzw ▸ huE ⟨z,hz,rfl⟩
    have hw0 := (hvE w hw).mp hvwE
    have hwM : w ∈ Minus := ⟨hw.1,by rw [hw0]; norm_num⟩
    exact hui hz hwM (huvzw.trans (huv ⟨hw.1,hw0⟩).symm)
  have hfi : InjOn f Box := by
    intro z hz w hw heq
    rcases hparts.symm.subset hz with hz | hz <;> rcases hparts.symm.subset hw with hw | hw
    · exact hui hz hw ((hfu' hz).symm.trans (heq.trans (hfu' hw)))
    · exact hcross z w hz hw heq
    · exact (hcross w z hw hz heq.symm).symm
    · exact hvi hz hw ((hfv' hz).symm.trans (heq.trans (hfv' hw)))
  obtain ⟨Q,hQs,hQt,hQi,hQf,hQ⟩ := exists_original_chart_of_ball_embedding he hb hf' hfi A
  have h0 : (0 : C3) ∈ interior Box := by
    change (0 : C3) ∈ interior ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1)
    simp only [interior_prod_eq,interior_Icc,mem_prod,mem_Ioo]
    norm_num
  have hf0 : f 0 = u 0 := hfu' ⟨⟨by norm_num,by norm_num⟩,by norm_num⟩
  refine ⟨f,Q,hf',hfi,hfu',hfv',hQs,hQt,hQi,hQf,?_,?_,hQ⟩
  · rw [hQs,←hf0]
    exact ⟨0,h0,rfl⟩
  · rw [←hf0,hQf 0 h0,map_zero]

theorem exists_original_marked_chart_of_glued_half_boxes
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {u v : C3 → X} {E S B F : Set X}
    (hu : PolyhedralPLInCharts e u Minus) (hui : InjOn u Minus)
    (hv : PolyhedralPLInCharts e v Plus) (hvi : InjOn v Plus)
    (huE : u '' Minus ⊆ E)
    (hvE : ∀ z ∈ Plus,v z ∈ E ↔ z.2 = 0)
    (huv : EqOn u v Base) (A : V3 ≃L[ℝ] C3)
    (huMarks : ∀ z ∈ Minus,
      (u z ∈ S ↔ z.1.1 = 0) ∧
      (u z ∈ B ↔ z.1.1 ≤ 0 ∧ z.1.2 ≤ 0) ∧ (u z ∈ F ↔ z.2 = 0))
    (hvMarks : ∀ z ∈ Plus,
      (v z ∈ S ↔ z.1.1 = 0) ∧
      (v z ∈ B ↔ z.1.1 ≤ 0 ∧ z.1.2 ≤ 0) ∧ (v z ∈ F ↔ z.2 = 0)) :
    ∃ Q : OpenPartialHomeomorph X V3,
      u 0 ∈ Q.source ∧ Q (u 0) = 0 ∧
      (∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source,y ∈ S ↔ (A (Q y)).1.1 = 0) ∧
      (∀ y ∈ Q.source,y ∈ B ↔ (A (Q y)).1.1 ≤ 0 ∧ (A (Q y)).1.2 ≤ 0) ∧
      ∀ y ∈ Q.source,y ∈ F ↔ (A (Q y)).2 = 0 := by
  obtain ⟨f,Q,hf,hfi,hfu,hfv,hQs,_,_,hQf,hxQ,hQx,hQ⟩ :=
    exists_original_chart_of_glued_half_boxes he hu hui hv hvi huE hvE huv A
  have hmarks (z : C3) (hz : z ∈ Box) :
      (f z ∈ S ↔ z.1.1 = 0) ∧
      (f z ∈ B ↔ z.1.1 ≤ 0 ∧ z.1.2 ≤ 0) ∧ (f z ∈ F ↔ z.2 = 0) := by
    by_cases ht : z.2 ≤ 0
    · have hzM : z ∈ Minus := ⟨hz.1,⟨hz.2.1,ht⟩⟩
      rw [hfu hzM]
      exact huMarks z hzM
    · have hzP : z ∈ Plus := ⟨hz.1,⟨(lt_of_not_ge ht).le,hz.2.2⟩⟩
      rw [hfv hzP]
      exact hvMarks z hzP
  have hvalues (y : X) (hy : y ∈ Q.source) :
      (y ∈ S ↔ (A (Q y)).1.1 = 0) ∧
      (y ∈ B ↔ (A (Q y)).1.1 ≤ 0 ∧ (A (Q y)).1.2 ≤ 0) ∧
      (y ∈ F ↔ (A (Q y)).2 = 0) := by
    obtain ⟨z,hz,rfl⟩ := hQs.subset hy
    rw [hQf z hz,A.apply_symm_apply]
    exact hmarks z (interior_subset hz)
  exact ⟨Q,hxQ,hQx,hQ,fun y hy => (hvalues y hy).1,
    fun y hy => (hvalues y hy).2.1,fun y hy => (hvalues y hy).2.2⟩

end PoincareConjecture.M76
