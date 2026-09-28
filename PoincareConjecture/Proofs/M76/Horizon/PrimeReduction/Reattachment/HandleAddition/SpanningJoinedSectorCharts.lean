import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCornerConfinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCornerSectorGluing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningSignedCornerChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningSidePairCharts

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Minus" => Set.prod (Set.prod (Icc (-1 : ℝ) 0) I) (Icc (0 : ℝ) 1)
local notation "Plus" => Set.prod (Set.prod (Icc (0 : ℝ) 1) I) (Icc (0 : ℝ) 1)
local notation "Base" => Set.prod (Set.prod ({0} : Set ℝ) I) (Icc (0 : ℝ) 1)

theorem ChartwisePLSphere.patch_corner_chart_of_joined_sectors
    {X V ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V3} {S W E F B Cap A Q T : Set X}
    (s : ChartwisePLSphere e S) (b : ChartwisePLBall e Q T)
    (hW : PLDomain e W) (hWS : frontier W = S)
    (hQ : Q = B ∪ Cap) (hBE : B ⊆ E) (hQW : Q ⊆ W)
    (hCapE : Cap ∩ E = A) (hBF : B ∩ F = A)
    {d q : Set V} (hd : IsFinitePLBallPair P2 d q)
    (p : V → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : Q ∩ S = p '' d) (hdT : p '' d ⊆ T)
    (hSout : (S \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty)
    {u v : C3 → X}
    (hu : PolyhedralPLInCharts e u Minus) (hui : InjOn u Minus)
    (hv : PolyhedralPLInCharts e v Plus) (hvi : InjOn v Plus)
    (huE : MapsTo u Minus E) (hvE : ∀ z ∈ Plus,v z ∈ E ↔ z.1.1 = 0)
    (huv : EqOn u v Base)
    (huMarks : ∀ z ∈ Minus,u z ∈ W ∧ (u z ∈ S ↔ z.2 = 0) ∧
      (u z ∈ F ↔ z.1.1 = 0) ∧ (u z ∈ B ↔ z.1.2 ≤ 0))
    (hvMarks : ∀ z ∈ Plus,v z ∈ W ∧ (v z ∈ S ↔ z.2 = 0) ∧
      (v z ∈ F ↔ z.1.1 = 0) ∧ (v z ∈ Cap ↔ z.1.2 ≤ 0))
    (H : OpenPartialHomeomorph X V3) (hxH : u 0 ∈ H.source) (hHx : H (u 0) = 0)
    (hHe : ∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (hHS : ∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0)
    (hHF : ∀ y ∈ H.source,y ∈ F ↔ H y 0 = 0) :
    ∃ G : OpenPartialHomeomorph X V3,
      u 0 ∈ G.source ∧ G (u 0) = 0 ∧
      (∀ i,(e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source,y ∈ (S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)) ↔ G y 1 = 0) ∧
      ∀ y ∈ G.source,y ∈ F ↔ G y 0 = 0 := by
  have hAB : A ⊆ B := hBF.symm.subset.trans inter_subset_left
  have hAC : A ⊆ Cap := hCapE.symm.subset.trans inter_subset_left
  have huQ (z : C3) (hz : z ∈ Minus) : u z ∈ Q ↔ z.1.2 ≤ 0 := by
    rw [hQ]
    constructor
    · rintro (h | h)
      · exact (huMarks z hz).2.2.2.mp h
      · exact (huMarks z hz).2.2.2.mp (hAB (hCapE.subset ⟨h,huE hz⟩))
    · exact fun h => Or.inl ((huMarks z hz).2.2.2.mpr h)
  have hvQ (z : C3) (hz : z ∈ Plus) : v z ∈ Q ↔ z.1.2 ≤ 0 := by
    rw [hQ]
    constructor
    · rintro (h | h)
      · have hz0 := (hvE z hz).mp (hBE h)
        have hzF := (hvMarks z hz).2.2.1.mpr hz0
        exact (hvMarks z hz).2.2.2.mp (hAC (hBF.subset ⟨h,hzF⟩))
      · exact (hvMarks z hz).2.2.2.mp h
    · exact fun h => Or.inr ((hvMarks z hz).2.2.2.mpr h)
  obtain ⟨f,hf,hfi,_,_,hf0,hfmarks⟩ :=
    exists_original_marked_corner_sector_gluing hW.compatible hu hui hv hvi
      (image_subset_iff.mpr huE) hvE huv
      (fun z hz => ⟨(huMarks z hz).1,(huMarks z hz).2.1,(huMarks z hz).2.2.1,huQ z hz⟩)
      (fun z hz => ⟨(hvMarks z hz).1,(hvMarks z hz).2.1,(hvMarks z hz).2.2.1,hvQ z hz⟩)
  have h0 : (0 : C3) ∈ Minus := by
    change (((0 : ℝ) ∈ Icc (-1) 0) ∧ ((0 : ℝ) ∈ I)) ∧ ((0 : ℝ) ∈ Icc 0 1)
    norm_num
  have hxS : u 0 ∈ S := (huMarks 0 h0).2.1.mpr rfl
  obtain ⟨B0,L,hxB,hBx,_,hBe,hBW,hBS,hBF0⟩ :=
    exists_signed_original_sphere_corner_chart hW hWS hxS H hxH hHx hHe hHS hHF
  obtain ⟨H0,hxH0,hH0x,hH0e,hH0S,hH0Q,hH0F⟩ :=
    exists_original_corner_chart_of_local_marked_sector B0 hBe L hxB hBx hQW hBW hBS hBF0
      f hf hfi hf0 (fun z hz => (hfmarks z hz).1) (fun z hz => (hfmarks z hz).2)
  obtain ⟨G,_,hxG,hGx,hGe,hGS,hGF⟩ := s.exists_original_ball_patch_corner_pair_chart b
    hW.compatible hd p hp hpi hcontact hdT hSout hTout H0 hH0e L hxH0 hH0x hH0S hH0Q hH0F
  exact ⟨G,hxG,hGx,hGe,hGS,hGF⟩

local notation "SideMinus" => Set.prod (Set.prod I I) (Icc (-1 : ℝ) 0)
local notation "SidePlus" => Set.prod (Set.prod I I) (Icc (0 : ℝ) 1)
local notation "SideBase" => Set.prod (Set.prod I I) ({0} : Set ℝ)

theorem ChartwisePLBall.patch_side_chart_of_joined_sectors
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S E F B Cap A Q T Patch Rim : Set X}
    (b : ChartwisePLBall e Q T)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hQ : Q = B ∪ Cap) (hBE : B ⊆ E)
    (hCapE : Cap ∩ E = A) (hBF : B ∩ F = A)
    (hS : IsClosed S) (hPatch : Patch ⊆ S)
    {u v : C3 → X}
    (hu : PolyhedralPLInCharts e u SideMinus) (hui : InjOn u SideMinus)
    (hv : PolyhedralPLInCharts e v SidePlus) (hvi : InjOn v SidePlus)
    (huE : MapsTo u SideMinus E) (hvE : ∀ z ∈ SidePlus,v z ∈ E ↔ z.2 = 0)
    (huv : EqOn u v SideBase) (hxS : u 0 ∉ S)
    (huMarks : ∀ z ∈ SideMinus,(u z ∈ F ↔ z.2 = 0) ∧ (u z ∈ B ↔ z.1.1 ≤ 0))
    (hvMarks : ∀ z ∈ SidePlus,(v z ∈ F ↔ z.2 = 0) ∧ (v z ∈ Cap ↔ z.1.1 ≤ 0)) :
    ∃ G : OpenPartialHomeomorph X V3,
      u 0 ∈ G.source ∧ G (u 0) = 0 ∧ G.source ⊆ Sᶜ ∧
      (∀ i,(e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source,y ∈ (S \ (Patch \ Rim)) ∪ (T \ (Patch \ Rim)) ↔ G y 1 = 0) ∧
      ∀ y ∈ G.source,y ∈ F ↔ G y 0 = 0 := by
  have hAB : A ⊆ B := hBF.symm.subset.trans inter_subset_left
  have hAC : A ⊆ Cap := hCapE.symm.subset.trans inter_subset_left
  have huQ (z : C3) (hz : z ∈ SideMinus) : u z ∈ Q ↔ z.1.1 ≤ 0 := by
    rw [hQ]
    constructor
    · rintro (h | h)
      · exact (huMarks z hz).2.mp h
      · exact (huMarks z hz).2.mp (hAB (hCapE.subset ⟨h,huE hz⟩))
    · exact fun h => Or.inl ((huMarks z hz).2.mpr h)
  have hvQ (z : C3) (hz : z ∈ SidePlus) : v z ∈ Q ↔ z.1.1 ≤ 0 := by
    rw [hQ]
    constructor
    · rintro (h | h)
      · have hz0 := (hvE z hz).mp (hBE h)
        have hzF := (hvMarks z hz).1.mpr hz0
        exact (hvMarks z hz).2.mp (hAC (hBF.subset ⟨h,hzF⟩))
      · exact (hvMarks z hz).2.mp h
    · exact fun h => Or.inr ((hvMarks z hz).2.mpr h)
  exact b.patch_pair_chart_of_glued_side_boxes hS hPatch he hu hui hv hvi
    (image_subset_iff.mpr huE) hvE huv
    (ContinuousLinearEquiv.ofFinrankEq (by simp)) hxS
    (fun z hz => ⟨huQ z hz,(huMarks z hz).1⟩)
    (fun z hz => ⟨hvQ z hz,(hvMarks z hz).1⟩)

end PoincareConjecture.M76
