import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.RimCoordinates

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "Phase" => Icc (-(1/2 : ℝ)) (3/2)

@[simp] theorem armPoint_lower (b : Bool) : armPoint b (-(1/2 : ℝ)) = ![0,-1] := by
  ext i
  fin_cases i <;> norm_num [armPoint]

@[simp] theorem armPoint_upper (b : Bool) : armPoint b (3/2 : ℝ) = ![0,1] := by
  ext i
  fin_cases i <;> norm_num [armPoint]

theorem armPhase_armPoint_closed (b : Bool) {t : ℝ} (ht : t ∈ Phase) :
    armPhase b (armPoint b t) = t := by
  rcases ht.1.eq_or_lt with h | h
  · rw [← h,armPoint_lower]
    norm_num [armPhase]
  · rcases ht.2.lt_or_eq with h' | h'
    · exact armPhase_armPoint b ⟨h,h'⟩
    · rw [h',armPoint_upper]
      norm_num [armPhase]

theorem armPoint_closed_mem (b : Bool) {t : ℝ} (ht : t ∈ Phase) :
    armPoint b t ∈ Rim ∧ 0 ≤ sign b * armPoint b t 0 := by
  rcases ht.1.eq_or_lt with h | h
  · rw [← h,armPoint_lower]
    constructor
    · rw [← CubeCoordinates.toRectangle_rim_iff,
        frontier_rectangle_eq_four_sides zero_le_one zero_le_one]
      left; left
      norm_num [CubeCoordinates.toRectangle_apply]
    · simp
  · rcases ht.2.lt_or_eq with h' | h'
    · exact ⟨(armPoint_mem b ⟨h,h'⟩).1,(armPoint_mem b ⟨h,h'⟩).2.le⟩
    · rw [h',armPoint_upper]
      constructor
      · rw [← CubeCoordinates.toRectangle_rim_iff,
          frontier_rectangle_eq_four_sides zero_le_one zero_le_one]
        left; right
        norm_num [CubeCoordinates.toRectangle_apply]
      · simp

theorem armPoint_closed_injective (b : Bool) : InjOn (armPoint b) Phase := by
  intro t ht s hs heq
  exact (armPhase_armPoint_closed b ht).symm.trans
    ((congrArg (armPhase b) heq).trans (armPhase_armPoint_closed b hs))

theorem armPoint_closed_image (b : Bool) :
    armPoint b '' Phase = Rim ∩ {z | 0 ≤ sign b * z 0} := by
  apply Subset.antisymm
  · rintro z ⟨t,ht,rfl⟩
    exact armPoint_closed_mem b ht
  · rintro z ⟨hz,hn⟩
    change 0 ≤ sign b * z 0 at hn
    rcases hn.eq_or_lt with h | h
    · have hz0 : z 0=0 := by cases b <;> simpa [sign] using h.symm
      have hf := (CubeCoordinates.toRectangle_rim_iff z).mpr hz
      rw [frontier_rectangle_eq_four_sides zero_le_one zero_le_one] at hf
      simp only [CubeCoordinates.toRectangle_apply,hz0,zero_add,mem_union,mem_prod,
        mem_singleton_iff] at hf
      rcases hf with (h | h) | (h | h)
      · refine ⟨-(1/2 : ℝ),by norm_num,?_⟩
        rw [armPoint_lower]
        ext i
        fin_cases i
        · exact hz0.symm
        · dsimp; linarith [h.2]
      · refine ⟨3/2,by norm_num,?_⟩
        rw [armPoint_upper]
        ext i
        fin_cases i
        · exact hz0.symm
        · dsimp; linarith [h.2]
      · norm_num at h
      · norm_num at h
    · exact ⟨armPhase b z,Ioo_subset_Icc_self (armPhase_mem b hz h),armPoint_armPhase b hz h⟩

theorem closed_arms_cover : (armPoint false '' Phase) ∪ (armPoint true '' Phase) = Rim := by
  rw [armPoint_closed_image,armPoint_closed_image]
  ext z
  simp only [mem_union,mem_inter_iff,mem_ofPred_eq,sign,Bool.false_eq_true,if_false,
    if_true,one_mul,neg_one_mul]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro hz
    rcases le_total 0 (z 0) with h | h
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,neg_nonneg.mpr h⟩

theorem closed_arms_overlap : (armPoint false '' Phase) ∩ (armPoint true '' Phase) =
    ({![0,-1],![0,1]} : Set V2) := by
  rw [armPoint_closed_image,armPoint_closed_image]
  ext z
  constructor
  · rintro ⟨⟨hz,hn⟩,⟨_,hm⟩⟩
    change 0 ≤ sign false * z 0 at hn
    change 0 ≤ sign true * z 0 at hm
    simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] at hn hm
    have hz0 : z 0=0 := le_antisymm (neg_nonneg.mp hm) hn
    have hf := (CubeCoordinates.toRectangle_rim_iff z).mpr hz
    rw [frontier_rectangle_eq_four_sides zero_le_one zero_le_one] at hf
    simp only [CubeCoordinates.toRectangle_apply,hz0,zero_add,mem_union,mem_prod,
      mem_singleton_iff] at hf
    rcases hf with (h | h) | (h | h)
    · left
      ext i
      fin_cases i
      · exact hz0
      · dsimp; linarith [h.2]
    · right
      ext i
      fin_cases i
      · exact hz0
      · dsimp; linarith [h.2]
    · norm_num at h
    · norm_num at h
  · rintro (rfl | rfl)
    · have hf := armPoint_closed_mem false (t := -(1/2 : ℝ)) (by norm_num)
      have ht := armPoint_closed_mem true (t := -(1/2 : ℝ)) (by norm_num)
      simpa only [armPoint_lower,mem_inter_iff,mem_ofPred_eq] using And.intro hf ht
    · have hf := armPoint_closed_mem false (t := 3/2) (by norm_num)
      have ht := armPoint_closed_mem true (t := 3/2) (by norm_num)
      simpa only [armPoint_upper,mem_inter_iff,mem_ofPred_eq] using And.intro hf ht

theorem armPoint_closed_finitePL (b : Bool) : FinitePiecewiseAffineOn (armPoint b) Phase := by
  have hb := isFinitePLBallPair_Icc (show -(1/2 : ℝ) < 3/2 by norm_num)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hb
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) Phase :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  exact finitePL_armPoint hid b

end PoincareConjecture.M76.Dehn.Annuli.RimBands
