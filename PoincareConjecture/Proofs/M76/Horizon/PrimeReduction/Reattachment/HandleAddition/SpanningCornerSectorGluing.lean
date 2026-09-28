import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Half" => Set.prod (Set.prod I I) (Icc (0 : ℝ) 1)
local notation "Minus" => Set.prod (Set.prod (Icc (-1 : ℝ) 0) I) (Icc (0 : ℝ) 1)
local notation "Plus" => Set.prod (Set.prod (Icc (0 : ℝ) 1) I) (Icc (0 : ℝ) 1)
local notation "Base" => Set.prod (Set.prod ({0} : Set ℝ) I) (Icc (0 : ℝ) 1)



theorem exists_original_marked_corner_sector_gluing
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {E W S F Q : Set X}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {u v : C3 → X}
    (hu : PolyhedralPLInCharts e u Minus) (hui : InjOn u Minus)
    (hv : PolyhedralPLInCharts e v Plus) (hvi : InjOn v Plus)
    (huE : u '' Minus ⊆ E) (hvE : ∀ z ∈ Plus,v z ∈ E ↔ z.1.1 = 0)
    (huv : EqOn u v Base)
    (huMarks : ∀ z ∈ Minus,u z ∈ W ∧ (u z ∈ S ↔ z.2 = 0) ∧
      (u z ∈ F ↔ z.1.1 = 0) ∧ (u z ∈ Q ↔ z.1.2 ≤ 0))
    (hvMarks : ∀ z ∈ Plus,v z ∈ W ∧ (v z ∈ S ↔ z.2 = 0) ∧
      (v z ∈ F ↔ z.1.1 = 0) ∧ (v z ∈ Q ↔ z.1.2 ≤ 0)) :
    ∃ f : C3 → X,
      PolyhedralPLInCharts e f Half ∧ InjOn f Half ∧
      EqOn f u Minus ∧ EqOn f v Plus ∧ f 0 = u 0 ∧
      ∀ z ∈ Half,f z ∈ W ∧ (f z ∈ S ↔ z.2 = 0) ∧
        (f z ∈ F ↔ z.1.1 = 0) ∧ (f z ∈ Q ↔ z.1.2 ≤ 0) := by
  have hI := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hP := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  have hM := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 0)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := (hM.prod hI).prod hP
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := (hP.prod hI).prod hP
  change K.space = Minus at hKs
  change L.space = Plus at hLs
  have hmeet : Minus ∩ Plus = Base := by
    ext z
    constructor
    · rintro ⟨hm,hp⟩
      exact ⟨⟨le_antisymm hm.1.1.2 hp.1.1.1,hm.1.2⟩,hm.2⟩
    · intro h
      exact ⟨⟨⟨by rw [h.1.1]; norm_num,h.1.2⟩,h.2⟩,
        ⟨⟨by rw [h.1.1]; norm_num,h.1.2⟩,h.2⟩⟩
  have hparts : Minus ∪ Plus = Half := by
    ext z
    constructor
    · rintro (h | h)
      · exact ⟨⟨⟨h.1.1.1,by linarith [h.1.1.2]⟩,h.1.2⟩,h.2⟩
      · exact ⟨⟨⟨by linarith [h.1.1.1],h.1.1.2⟩,h.1.2⟩,h.2⟩
    · intro h
      by_cases hz : z.1.1 ≤ 0
      · exact Or.inl ⟨⟨⟨h.1.1.1,hz⟩,h.1.2⟩,h.2⟩
      · exact Or.inr ⟨⟨⟨(lt_of_not_ge hz).le,h.1.1.2⟩,h.1.2⟩,h.2⟩
  obtain ⟨f,hf,hfu,hfv⟩ := _root_.Dehn.exists_circle_attachment_map_union he K L hK hL
    (hKs.symm ▸ hu) (hLs.symm ▸ hv)
    (fun z hz hz' => huv (hmeet.subset ⟨hKs.subset hz,hLs.subset hz'⟩))
  have hf' : PolyhedralPLInCharts e f Half := by simpa only [hKs,hLs,hparts] using hf
  have hfu' : EqOn f u Minus := hKs ▸ hfu
  have hfv' : EqOn f v Plus := hLs ▸ hfv
  have hcross (z w : C3) (hz : z ∈ Minus) (hw : w ∈ Plus) (heq : f z = f w) : z = w := by
    have huvzw : u z = v w := (hfu' hz).symm.trans (heq.trans (hfv' hw))
    have hw0 := (hvE w hw).mp (huvzw ▸ huE ⟨z,hz,rfl⟩)
    have hwM : w ∈ Minus := ⟨⟨by rw [hw0]; norm_num,hw.1.2⟩,hw.2⟩
    exact hui hz hwM (huvzw.trans (huv ⟨⟨hw0,hw.1.2⟩,hw.2⟩).symm)
  have hfi : InjOn f Half := by
    intro z hz w hw heq
    rcases hparts.symm.subset hz with hz | hz <;> rcases hparts.symm.subset hw with hw | hw
    · exact hui hz hw ((hfu' hz).symm.trans (heq.trans (hfu' hw)))
    · exact hcross z w hz hw heq
    · exact (hcross w z hw hz heq.symm).symm
    · exact hvi hz hw ((hfv' hz).symm.trans (heq.trans (hfv' hw)))
  refine ⟨f,hf',hfi,hfu',hfv',hfu' ⟨⟨by norm_num,by norm_num⟩,by norm_num⟩,?_⟩
  intro z hz
  rcases hparts.symm.subset hz with hz | hz
  · rw [hfu' hz]
    exact huMarks z hz
  · rw [hfv' hz]
    exact hvMarks z hz

end PoincareConjecture.M76
