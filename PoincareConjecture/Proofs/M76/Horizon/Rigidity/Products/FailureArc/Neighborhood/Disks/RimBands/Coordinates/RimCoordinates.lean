import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.ArmIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "Rim" => sphere (0 : V2) 1

def armPhase (b : Bool) (z : V2) : ℝ :=
  (z 1 + max 0 (z 1 - sign b * z 0) - max 0 (-z 1 - sign b * z 0) + 1) / 2

def armPoint (b : Bool) (t : ℝ) : V2 :=
  ![sign b * (1 - 2 * max 0 (-t) - 2 * max 0 (t-1)),
    2*t-1 + 2*max 0 (-t) - 2*max 0 (t-1)]

theorem continuous_armPhase (b : Bool) : Continuous (armPhase b) := by
  unfold armPhase
  fun_prop

theorem continuous_armPoint (b : Bool) : Continuous (armPoint b) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [armPoint] <;> fun_prop

theorem armPoint_eq_rimArm (b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    armPoint b t = rimArm b t := by
  simp [armPoint,rimArm,max_eq_left (neg_nonpos.mpr ht.1),
    max_eq_left (sub_nonpos.mpr ht.2)]

theorem armPhase_rimArm (b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    armPhase b (rimArm b t) = t := by
  have h0 : 2*t-1-1 ≤ 0 := by linarith [ht.2]
  have h1 : -(2*t-1)-1 ≤ 0 := by linarith [ht.1]
  cases b <;> simp only [armPhase,rimArm,sign,Bool.false_eq_true,if_false,if_true,
    Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,neg_one_mul,neg_neg]
  all_goals rw [max_eq_left h0,max_eq_left h1]; ring

private theorem rim_coordinates {z : V2} (hz : z ∈ Rim) :
    (-1 ≤ z 0 ∧ z 0 ≤ 1) ∧ (-1 ≤ z 1 ∧ z 1 ≤ 1) ∧
      (z 0 = -1 ∨ z 0 = 1 ∨ z 1 = -1 ∨ z 1 = 1) := by
  have hd := (CubeCoordinates.mem_disk_iff z).mp (sphere_subset_closedBall hz)
  have hf := (CubeCoordinates.toRectangle_rim_iff z).mpr hz
  rw [frontier_rectangle_eq_four_sides zero_le_one zero_le_one] at hf
  simp only [CubeCoordinates.toRectangle_apply,mem_union,mem_prod,mem_singleton_iff] at hf
  refine ⟨hd.1,hd.2,?_⟩
  rcases hf with (h | h) | (h | h)
  · exact Or.inr (Or.inr (Or.inl (by linarith [h.2])))
  · exact Or.inr (Or.inr (Or.inr (by linarith [h.2])))
  · exact Or.inl (by linarith [h.1])
  · exact Or.inr (Or.inl (by linarith [h.1]))

set_option maxHeartbeats 800000 in
theorem armPoint_armPhase (b : Bool) {z : V2} (hz : z ∈ Rim)
    (hs : 0 < sign b * z 0) : armPoint b (armPhase b z) = z := by
  obtain ⟨h0,h1,hside⟩ := rim_coordinates hz
  have hsign : sign b * sign b = 1 := by cases b <;> norm_num [sign]
  have hn : 0 < sign b * z 0 ∧ sign b * z 0 ≤ 1 := by
    refine ⟨hs,?_⟩
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] <;>
      linarith [h0.1,h0.2]
  have hside' : sign b * z 0 = 1 ∨ z 1 = -1 ∨ z 1 = 1 := by
    rcases hside with h | h | h | h
    · cases b <;> simp_all [sign]
      all_goals linarith
    · cases b <;> simp_all [sign]
      all_goals linarith
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] at *
  all_goals
    funext i
    fin_cases i <;> dsimp [armPoint,armPhase,sign]
    all_goals
      rcases hside' with h | h | h
      all_goals
        simp only [max_def]
        split_ifs <;> linarith [hn.1,hn.2,h0.1,h0.2,h1.1,h1.2]

theorem armPoint_mem (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-(1/2 : ℝ)) (3/2)) :
    armPoint b t ∈ Rim ∧ 0 < sign b * armPoint b t 0 := by
  have hlo : max 0 (-t) = if t ≤ 0 then -t else 0 := by
    split_ifs <;> simp_all
    all_goals linarith
  have hhi : max 0 (t-1) = if 1 ≤ t then t-1 else 0 := by
    split_ifs <;> simp_all
    all_goals linarith
  constructor
  · rw [← CubeCoordinates.toRectangle_rim_iff,
      frontier_rectangle_eq_four_sides zero_le_one zero_le_one]
    simp only [CubeCoordinates.toRectangle_apply,armPoint,Matrix.cons_val_zero,
      Matrix.cons_val_one,hlo,hhi]
    by_cases h0 : t ≤ 0
    · have h1 : ¬ 1 ≤ t := by linarith
      simp only [if_pos h0,if_neg h1]
      apply Or.inl; apply Or.inl
      constructor
      · cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
        all_goals constructor <;> linarith [ht.1]
      · simp only [mem_singleton_iff]; ring
    · by_cases h1 : 1 ≤ t
      · simp only [if_neg h0,if_pos h1]
        apply Or.inl; apply Or.inr
        constructor
        · cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
          all_goals constructor <;> linarith [ht.2]
        · simp only [mem_singleton_iff]; ring
      · simp only [if_neg h0,if_neg h1,mul_zero,sub_zero,add_zero]
        cases b
        · apply Or.inr; apply Or.inr
          constructor
          · norm_num [sign]
          · constructor <;> linarith
        · apply Or.inr; apply Or.inl
          constructor
          · norm_num [sign]
          · constructor <;> linarith
  · simp only [armPoint,Matrix.cons_val_zero,hlo,hhi]
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,neg_neg]
    all_goals split_ifs <;> linarith [ht.1,ht.2]

set_option maxHeartbeats 400000 in
theorem armPhase_armPoint (b : Bool) {t : ℝ}
    (ht : t ∈ Ioo (-(1/2 : ℝ)) (3/2)) : armPhase b (armPoint b t) = t := by
  cases b <;> dsimp [armPhase,armPoint,sign]
  all_goals simp only [max_def]; split_ifs <;> linarith [ht.1,ht.2]

theorem armPhase_mem (b : Bool) {z : V2} (hz : z ∈ Rim)
    (hs : 0 < sign b * z 0) : armPhase b z ∈ Ioo (-(1/2 : ℝ)) (3/2) := by
  obtain ⟨h0,h1,_⟩ := rim_coordinates hz
  cases b <;> dsimp [armPhase,sign] at *
  all_goals simp only [max_def]; split_ifs <;> constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

def armHomeomorph (b : Bool) :
    {z : V2 | z ∈ Rim ∧ 0 < sign b * z 0} ≃ₜ Ioo (-(1/2 : ℝ)) (3/2) where
  toFun z := ⟨armPhase b z,armPhase_mem b z.2.1 z.2.2⟩
  invFun t := ⟨armPoint b t,armPoint_mem b t.2⟩
  left_inv z := Subtype.ext (armPoint_armPhase b z.2.1 z.2.2)
  right_inv t := Subtype.ext (armPhase_armPoint b t.2)
  continuous_toFun := (continuous_armPhase b).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (continuous_armPoint b).comp continuous_subtype_val |>.subtype_mk _

theorem finitePL_armPhase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {f : E → V2}
    (hf : FinitePiecewiseAffineOn f S) (b : Bool) :
    FinitePiecewiseAffineOn (armPhase b ∘ f) S := by
  let n := (sign b • (ContinuousLinearMap.proj (0 : Fin 2) : V2 →L[ℝ] ℝ)).toContinuousAffineMap
  let y := (ContinuousLinearMap.proj (1 : Fin 2) : V2 →L[ℝ] ℝ).toContinuousAffineMap
  have hn := hf.postcomp n
  have hy := hf.postcomp y
  have hny := hf.postcomp (-y)
  let A : ℝ →ᴬ[ℝ] ℝ := (1/2 : ℝ) •
    ((ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap + ContinuousAffineMap.const ℝ ℝ 1)
  convert ((hy.add (hy.sub hn).positivePart).sub (hny.sub hn).positivePart).postcomp A using 1
  ext x
  simp [armPhase,n,y,A,div_eq_mul_inv,mul_comm]
  ring

theorem finitePL_armPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {f : E → ℝ}
    (hf : FinitePiecewiseAffineOn f S) (b : Bool) :
    FinitePiecewiseAffineOn (armPoint b ∘ f) S := by
  let A : ℝ →ᴬ[ℝ] ℝ := (ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  let C : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1
  have hneg := (hf.postcomp (-A)).positivePart
  have hpos := (hf.postcomp (A-C)).positivePart
  let scale : ℝ →ᴬ[ℝ] ℝ := (2 : ℝ) • A
  have hn := ((hf.postcomp C).sub (hneg.postcomp scale)).sub (hpos.postcomp scale)
  have hy := ((hf.postcomp (scale-C)).add (hneg.postcomp scale)).sub (hpos.postcomp scale)
  have hpair := (hn.postcomp (sign b • A)).prod_mk hy
  convert hpair.postcomp
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearMap.toContinuousAffineMap using 1
  ext x i
  fin_cases i <;> simp [armPoint,A,C,scale]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
