import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoIntervalDiskNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall









set_option autoImplicit false
open Set Metric Geometry
open scoped unitInterval
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rect" => Set.prod (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)

private def lowerCorner : P2 →ᴬ[ℝ] V2 :=
  ContinuousAffineMap.const ℝ P2 (fun _ : Fin 2 => (-1 : ℝ)) +
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousAffineEquiv.toContinuousAffineMap

private theorem lowerCorner_mem_disk {x : P2} (hx : x ∈ Rect) : lowerCorner x ∈ Disk := by
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro i
  fin_cases i
  · change |(-1 : ℝ) + x.1| ≤ 1
    rw [abs_le]
    constructor <;> linarith [hx.1.1,hx.1.2]
  · change |(-1 : ℝ) + x.2| ≤ 1
    rw [abs_le]
    constructor <;> linarith [hx.2.1,hx.2.2]

private theorem lowerCorner_first_half {x : P2} (hx : x ∈ Rect) :
    lowerCorner x ∈ Dehn.squareRimHalfCarrier false ↔ x.2 = 0 := by
  constructor
  · rintro ⟨t,ht⟩
    rw [Dehn.squareRimHalf_coordinates] at ht
    simp only [Bool.false_eq_true,if_false] at ht
    split_ifs at ht with h
    · have hh := congrFun ht 1
      change (-1 : ℝ) = -1+x.2 at hh
      linarith
    · have hh := congrFun ht 0
      change (1 : ℝ) = -1+x.1 at hh
      linarith [hx.1.2]
  · intro h
    let t : unitInterval := ⟨x.1/4,by constructor <;> linarith [hx.1.1,hx.1.2]⟩
    refine ⟨t,?_⟩
    rw [Dehn.squareRimHalf_coordinates]
    have ht : (t : ℝ) ≤ 1/2 := by dsimp [t]; linarith [hx.1.2]
    simp only [Bool.false_eq_true,if_false,if_pos ht]
    ext i
    fin_cases i
    · change -1+4*(x.1/4) = -1+x.1
      ring
    · change -1 = -1+x.2
      rw [h,add_zero]

private theorem lowerCorner_second_half {x : P2} (hx : x ∈ Rect) :
    lowerCorner x ∈ Dehn.squareRimHalfCarrier true ↔ x.1 = 0 := by
  constructor
  · rintro ⟨t,ht⟩
    rw [Dehn.squareRimHalf_coordinates] at ht
    simp only [if_true] at ht
    split_ifs at ht with h
    · have hh := congrFun ht 0
      change (-1 : ℝ) = -1+x.1 at hh
      linarith
    · have hh := congrFun ht 1
      change (1 : ℝ) = -1+x.2 at hh
      linarith [hx.2.2]
  · intro h
    let t : unitInterval := ⟨x.2/4,by constructor <;> linarith [hx.2.1,hx.2.2]⟩
    refine ⟨t,?_⟩
    rw [Dehn.squareRimHalf_coordinates]
    have ht : (t : ℝ) ≤ 1/2 := by dsimp [t]; linarith [hx.2.2]
    simp only [if_true,if_pos ht]
    ext i
    fin_cases i
    · change -1 = -1+x.1
      rw [h,add_zero]
    · change -1+4*(x.2/4) = -1+x.2
      ring




theorem exists_marked_disk_endpoint_quadrant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d U C : Set E} {a b : E}
    (hd : IsFinitePLBallPair P2 d (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hC : IsFinitePLBallPair ℝ C {a,b})
    (hab : a ≠ b) (hUC : U ∩ C = {a,b}) :
    ∃ q : P2 → E,
      FinitePiecewiseAffineOn q Rect ∧ InjOn q Rect ∧ MapsTo q Rect d ∧ q 0 = a ∧
      (∀ z ∈ Rect,q z ∈ U ↔ z.2 = 0) ∧
      ∀ z ∈ Rect,q z ∈ C ↔ z.1 = 0 := by
  obtain ⟨p,hp,hp0,hp1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨r,hr,hr0,hr1⟩ := hC.exists_unitInterval_chart_with_endpoints hab
  change (p (0 : unitInterval) : E) = a at hp0
  obtain ⟨_,f,_,hf,hfemb,himage,_,_,hfp,hfr,_⟩ :=
    Dehn.exists_two_interval_disk_normalization hd hab hUC p r hp hr hp0 hp1 hr0 hr1
  have hfi : InjOn f Disk := fun x hx y hy hxy => congrArg Subtype.val
    (hfemb.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hmarks (second : Bool) (x : V2) (hx : x ∈ Disk) :
      f x ∈ (if second then C else U) ↔ x ∈ Dehn.squareRimHalfCarrier second := by
    have hparam (t : unitInterval) :
        f (Dehn.squareRimHalf second t) = if second then (r t : E) else (p t : E) := by
      cases second
      · exact hfp t
      · exact hfr t
    constructor
    · intro hxM
      have hsurj : ∃ t : unitInterval,(if second then (r t : E) else (p t : E)) = f x := by
        cases second
        · exact ⟨p.symm ⟨f x,hxM⟩,congrArg Subtype.val (p.apply_symm_apply _)⟩
        · exact ⟨r.symm ⟨f x,hxM⟩,congrArg Subtype.val (r.apply_symm_apply _)⟩
      obtain ⟨t,ht⟩ := hsurj
      exact ⟨t,hfi (sphere_subset_closedBall (Dehn.squareRimHalfCarrier_subset second ⟨t,rfl⟩)) hx
        ((hparam t).trans ht)⟩
    · rintro ⟨t,rfl⟩
      rw [hparam]
      cases second
      · exact (p t).property
      · exact (r t).property
  have hA : FinitePiecewiseAffineOn lowerCorner Rect := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
      (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
        (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    exact ⟨K,hK,hKs,K.affineOnFaces_affine lowerCorner⟩
  let q := f ∘ lowerCorner
  have hq : FinitePiecewiseAffineOn q Rect := hf.comp hA (fun _ hx => lowerCorner_mem_disk hx)
  have hqi : InjOn q Rect := by
    intro x hx y hy hxy
    have hh := hfi (lowerCorner_mem_disk hx) (lowerCorner_mem_disk hy) hxy
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    change -1+x.1 = -1+y.1 at h0
    change -1+x.2 = -1+y.2 at h1
    exact Prod.ext (by linarith) (by linarith)
  refine ⟨q,hq,hqi,fun x hx => himage.subset ⟨lowerCorner x,lowerCorner_mem_disk hx,rfl⟩,?_,?_,?_⟩
  · have hh := hfp (0 : unitInterval)
    change f (Dehn.squareRimHalf false 0) = p (0 : unitInterval) at hh
    rw [Dehn.squareRimHalf_zero,hp0] at hh
    have h0 : lowerCorner 0 = (Dehn.squareRimBase : V2) := by
      ext i
      fin_cases i <;> norm_num [lowerCorner,Dehn.squareRimBase,Dehn.squareRimVertex]
    change f (lowerCorner 0) = a
    rw [h0]
    exact hh
  · intro x hx
    exact (hmarks false (lowerCorner x) (lowerCorner_mem_disk hx)).trans (lowerCorner_first_half hx)
  · intro x hx
    exact (hmarks true (lowerCorner x) (lowerCorner_mem_disk hx)).trans (lowerCorner_second_half hx)

end PoincareConjecture.M76

