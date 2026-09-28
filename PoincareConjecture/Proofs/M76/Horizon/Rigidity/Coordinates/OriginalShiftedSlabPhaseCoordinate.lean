import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalCircleCoordinate
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleSlab
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

private theorem coe_mem_shifted_closedIntervalArc_iff {c a b t : ℝ}
    (ha : c ≤ a) (hb : b < c + 4 * 16) (ht : t ∈ Ico c (c + 4 * 16)) :
    (t : C0) ∈ AddCircle.closedIntervalArc (4 * 16) a b ↔ t ∈ Icc a b := by
  constructor
  · rintro ⟨s, hs, hst⟩
    have hsI : s ∈ Ico c (c + 4 * 16) :=
      ⟨ha.trans hs.1, hs.2.trans_lt hb⟩
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hsI ht).mp hst
    exact heq ▸ hs
  · intro ht'
    exact ⟨t, ht', rfl⟩



theorem ChartwisePLMap.exists_hamiltonZero_shifted_lower_slab_coordinate {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + 4 * 16)
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)}) :
    let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
    ∃ (f : X0 → ℝ) (U : Set X0), IsOpen U ∧ ContinuousOn f U ∧
      (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' U)) ∧
      (∀ x ∈ U, hamiltonZeroCircleMap phi x = (a : C0) + (f x : C0)) ∧
      (∀ x ∈ U, x ∈ interior R ↔ 0 < f x) ∧
      (∀ x ∈ U, x ∈ frontier R ↔ f x = 0) ∧
      (∀ x ∈ U, |f x| < b - a) ∧
      ∀ x ∈ R, hamiltonZeroCircleMap phi x ≠ (b : C0) → x ∈ U := by
  intro R
  let q := hamiltonZeroCircleMap phi
  let C := AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) c
  let W := q ⁻¹' C.target
  let f := fun x => C.symm (q x) - a
  have hW : IsOpen W := C.open_target.preimage q.continuous
  have hfc : ContinuousOn f W :=
    (C.symm.continuousOn.comp q.continuous.continuousOn (fun _ hx => hx)).sub continuousOn_const
  let U := W ∩ f ⁻¹' Ioo (-(b - a)) (b - a)
  have hU : IsOpen U := hfc.isOpen_inter_preimage hW isOpen_Ioo
  have hrep (x : X0) (hx : x ∈ W) : C.symm (q x) ∈ Ioo c (c + 4 * 16) := by
    simpa only [C, AddCircle.openPartialHomeomorphCoe_source] using C.map_target hx
  have hqrep (x : X0) (hx : x ∈ W) : ((C.symm (q x) : ℝ) : C0) = q x := C.right_inv hx
  have haI : a ∈ Ico c (c + 4 * 16) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico c (c + 4 * 16) := ⟨by linarith, by linarith⟩
  have hsign (x : X0) (hx : x ∈ U) :
      (x ∈ R ↔ 0 ≤ f x) ∧ (x ∈ frontier R ↔ f x = 0) := by
    have hs := hrep x hx.1
    have hsI : C.symm (q x) ∈ Ico c (c + 4 * 16) := ⟨hs.1.le, by linarith [hs.2]⟩
    have hsb : C.symm (q x) < b := by
      have h := hx.2.2
      change C.symm (q x) - a < b - a at h
      linarith
    have hRiff : x ∈ R ↔ 0 ≤ f x := by
      change q x ∈ AddCircle.closedIntervalArc (4 * 16) a b ↔ 0 ≤ C.symm (q x) - a
      conv_lhs => rw [← hqrep x hx.1,
        coe_mem_shifted_closedIntervalArc_iff ha.le hb ⟨hs.1.le, hs.2⟩]
      exact ⟨fun h => sub_nonneg.mpr h.1, fun h => ⟨sub_nonneg.mp h, hsb.le⟩⟩
    refine ⟨hRiff, ?_⟩
    rw [hfront]
    change q x = (a : C0) ∨ q x = (b : C0) ↔ C.symm (q x) - a = 0
    conv_lhs => rw [← hqrep x hx.1,
      AddCircle.coe_eq_coe_iff_of_mem_Ico hsI haI,
      AddCircle.coe_eq_coe_iff_of_mem_Ico hsI hbI]
    exact ⟨fun h => sub_eq_zero.mpr (h.resolve_right hsb.ne),
      fun h => Or.inl (sub_eq_zero.mp h)⟩
  refine ⟨f, U, hU, hfc.mono inter_subset_left, ?_, ?_, ?_,
    fun x hx => (hsign x hx).2, fun x hx => abs_lt.mpr hx.2, ?_⟩
  · intro i
    have hlocal := hphi.locallyPL_hamiltonZero_circle_coordinate hd c i
    let ell : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ a
    have h := (locallyPiecewiseAffineOn_affine ell isOpen_univ).comp hlocal
    rw [preimage_univ, inter_univ] at h
    have hUi : IsOpen ((e i).target ∩ (e i).symm ⁻¹' U) :=
      (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    exact (h.mono hUi (fun _ hx => ⟨hx.1, hx.2.1⟩)).congr (fun _ _ => rfl)
  · intro x hx
    rw [← hqrep x hx.1]
    change ((C.symm (q x) : ℝ) : C0) = (a : C0) + ((C.symm (q x) - a : ℝ) : C0)
    rw [AddCircle.coe_sub]
    abel
  · intro x hx
    constructor
    · intro hi
      have hnonneg := (hsign x hx).1.mp (interior_subset hi)
      apply lt_of_le_of_ne hnonneg
      intro hz
      exact disjoint_left.mp disjoint_interior_frontier hi ((hsign x hx).2.mpr hz.symm)
    · intro hp
      apply (mem_interior_iff_notMem_frontier ((hsign x hx).1.mpr hp.le)).mpr
      exact fun hf => hp.ne' ((hsign x hx).2.mp hf)
  · intro x hx hxb
    obtain ⟨t, ht, htq⟩ := hx
    have htC : t ∈ C.source := by
      change c < t ∧ t < c + 4 * 16
      constructor <;> linarith [ht.1, ht.2]
    have hxW : x ∈ W := by
      change q x ∈ C.target
      rw [← htq]
      exact C.map_source htC
    have hft : f x = t - a := by
      change C.symm (q x) - a = t - a
      rw [← htq]
      exact congrArg (fun t : ℝ => t - a) (C.left_inv htC)
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => hxb (htq.symm.trans (congrArg (fun t : ℝ => (t : C0)) h)))
    refine ⟨hxW, ?_⟩
    change f x ∈ Ioo (-(b - a)) (b - a)
    rw [hft]
    constructor <;> linarith [ht.1]



theorem ChartwisePLMap.exists_hamiltonZero_shifted_upper_slab_coordinate {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + 4 * 16)
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)}) :
    let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
    ∃ (f : X0 → ℝ) (U : Set X0), IsOpen U ∧ ContinuousOn f U ∧
      (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' U)) ∧
      (∀ x ∈ U, hamiltonZeroCircleMap phi x = (b : C0) - (f x : C0)) ∧
      (∀ x ∈ U, x ∈ interior R ↔ 0 < f x) ∧
      (∀ x ∈ U, x ∈ frontier R ↔ f x = 0) ∧
      (∀ x ∈ U, |f x| < b - a) ∧
      ∀ x ∈ R, hamiltonZeroCircleMap phi x ≠ (a : C0) → x ∈ U := by
  intro R
  let q := hamiltonZeroCircleMap phi
  let C := AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) c
  let W := q ⁻¹' C.target
  let f := fun x => b - C.symm (q x)
  have hW : IsOpen W := C.open_target.preimage q.continuous
  have hfc : ContinuousOn f W :=
    continuousOn_const.sub
      (C.symm.continuousOn.comp q.continuous.continuousOn (fun _ hx => hx))
  let U := W ∩ f ⁻¹' Ioo (-(b - a)) (b - a)
  have hU : IsOpen U := hfc.isOpen_inter_preimage hW isOpen_Ioo
  have hrep (x : X0) (hx : x ∈ W) : C.symm (q x) ∈ Ioo c (c + 4 * 16) := by
    simpa only [C, AddCircle.openPartialHomeomorphCoe_source] using C.map_target hx
  have hqrep (x : X0) (hx : x ∈ W) : ((C.symm (q x) : ℝ) : C0) = q x := C.right_inv hx
  have haI : a ∈ Ico c (c + 4 * 16) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico c (c + 4 * 16) := ⟨by linarith, by linarith⟩
  have hsign (x : X0) (hx : x ∈ U) :
      (x ∈ R ↔ 0 ≤ f x) ∧ (x ∈ frontier R ↔ f x = 0) := by
    have hs := hrep x hx.1
    have hsI : C.symm (q x) ∈ Ico c (c + 4 * 16) := ⟨hs.1.le, by linarith [hs.2]⟩
    have hsa : a < C.symm (q x) := by
      have h := hx.2.2
      change b - C.symm (q x) < b - a at h
      linarith
    have hRiff : x ∈ R ↔ 0 ≤ f x := by
      change q x ∈ AddCircle.closedIntervalArc (4 * 16) a b ↔ 0 ≤ b - C.symm (q x)
      conv_lhs => rw [← hqrep x hx.1,
        coe_mem_shifted_closedIntervalArc_iff ha.le hb ⟨hs.1.le, hs.2⟩]
      exact ⟨fun h => sub_nonneg.mpr h.2, fun h => ⟨hsa.le, sub_nonneg.mp h⟩⟩
    refine ⟨hRiff, ?_⟩
    rw [hfront]
    change q x = (a : C0) ∨ q x = (b : C0) ↔ b - C.symm (q x) = 0
    conv_lhs => rw [← hqrep x hx.1,
      AddCircle.coe_eq_coe_iff_of_mem_Ico hsI haI,
      AddCircle.coe_eq_coe_iff_of_mem_Ico hsI hbI]
    exact ⟨fun h => sub_eq_zero.mpr (h.resolve_left hsa.ne').symm,
      fun h => Or.inr (sub_eq_zero.mp h).symm⟩
  refine ⟨f, U, hU, hfc.mono inter_subset_left, ?_, ?_, ?_,
    fun x hx => (hsign x hx).2, fun x hx => abs_lt.mpr hx.2, ?_⟩
  · intro i
    have hlocal := hphi.locallyPL_hamiltonZero_circle_coordinate hd c i
    let ell : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ b - ContinuousAffineMap.id ℝ ℝ
    have h := (locallyPiecewiseAffineOn_affine ell isOpen_univ).comp hlocal
    rw [preimage_univ, inter_univ] at h
    have hUi : IsOpen ((e i).target ∩ (e i).symm ⁻¹' U) :=
      (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    exact (h.mono hUi (fun _ hx => ⟨hx.1, hx.2.1⟩)).congr (fun _ _ => rfl)
  · intro x hx
    rw [← hqrep x hx.1]
    change ((C.symm (q x) : ℝ) : C0) = (b : C0) - ((b - C.symm (q x) : ℝ) : C0)
    rw [AddCircle.coe_sub]
    abel
  · intro x hx
    constructor
    · intro hi
      have hnonneg := (hsign x hx).1.mp (interior_subset hi)
      apply lt_of_le_of_ne hnonneg
      intro hz
      exact disjoint_left.mp disjoint_interior_frontier hi ((hsign x hx).2.mpr hz.symm)
    · intro hp
      apply (mem_interior_iff_notMem_frontier ((hsign x hx).1.mpr hp.le)).mpr
      exact fun hf => hp.ne' ((hsign x hx).2.mp hf)
  · intro x hx hxa
    obtain ⟨t, ht, htq⟩ := hx
    have htC : t ∈ C.source := by
      change c < t ∧ t < c + 4 * 16
      constructor <;> linarith [ht.1, ht.2]
    have hxW : x ∈ W := by
      change q x ∈ C.target
      rw [← htq]
      exact C.map_source htC
    have hft : f x = b - t := by
      change b - C.symm (q x) = b - t
      rw [← htq]
      exact congrArg (fun t : ℝ => b - t) (C.left_inv htC)
    have hat : a < t := lt_of_le_of_ne ht.1 (fun h =>
      hxa (htq.symm.trans (congrArg (fun t : ℝ => (t : C0)) h.symm)))
    refine ⟨hxW, ?_⟩
    change f x ∈ Ioo (-(b - a)) (b - a)
    rw [hft]
    constructor <;> linarith [ht.2]

end PoincareConjecture.M76

