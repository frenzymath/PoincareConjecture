import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.SlabCoordinate

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩




theorem exists_hamiltonZero_shifted_upper_second_slab_coordinate
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0), (b : C0)})) :
    let q := hamiltonZeroSecondCircleMap phi
    let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
    ∃ (f : X0 → ℝ) (U : Set X0), IsOpen U ∧ U ⊆ interior R ∧ ContinuousOn f U ∧
      (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' U)) ∧
      (∀ x ∈ U, q x = (b : C0) - (f x : C0)) ∧
      (∀ x ∈ U, x ∈ interior N ↔ 0 < f x) ∧
      (∀ x ∈ U, x ∈ frontier N ↔ f x = 0) ∧
      (∀ x ∈ U, |f x| < b - a) ∧
      ∀ x ∈ N, x ∉ frontier R → q x ≠ (a : C0) → x ∈ U := by
  intro q N
  let A := AddCircle.openPartialHomeomorphCoe p c
  let W := interior R ∩ q ⁻¹' A.target
  let f := fun x => b - A.symm (q x)
  have hW : IsOpen W := isOpen_interior.inter (A.open_target.preimage q.continuous)
  have hfc : ContinuousOn f W :=
    continuousOn_const.sub
      (A.symm.continuousOn.comp q.continuous.continuousOn (fun _ hx => hx.2))
  let U := W ∩ f ⁻¹' Ioo (-(b - a)) (b - a)
  have hU : IsOpen U := hfc.isOpen_inter_preimage hW isOpen_Ioo
  have hrep (x : X0) (hx : x ∈ W) : A.symm (q x) ∈ Ioo c (c + p) := by
    simpa only [A, AddCircle.openPartialHomeomorphCoe_source] using A.map_target hx.2
  have hqrep (x : X0) (hx : x ∈ W) : ((A.symm (q x) : ℝ) : C0) = q x := A.right_inv hx.2
  have haI : a ∈ Ico c (c + p) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico c (c + p) := ⟨by linarith, by linarith⟩
  have hsign (x : X0) (hx : x ∈ U) :
      (x ∈ N ↔ 0 ≤ f x) ∧ (x ∈ frontier N ↔ f x = 0) := by
    have hxR : x ∈ R := interior_subset hx.1.1
    have hs := hrep x hx.1
    have hsI : A.symm (q x) ∈ Ico c (c + p) := ⟨hs.1.le, hs.2⟩
    have hsa : a < A.symm (q x) := by
      have h := hx.2.2
      change b - A.symm (q x) < b - a at h
      linarith
    have hmem : x ∈ N ↔ q x ∈ AddCircle.closedIntervalArc p a b := and_iff_right hxR
    have hNiff : x ∈ N ↔ 0 ≤ f x := by
      rw [hmem, ← hqrep x hx.1, (AddCircle.coe_mem_closedIntervalArc_shifted_iff p) ha.le hb hsI]
      exact ⟨fun h => sub_nonneg.mpr h.2, fun h => ⟨hsa.le, sub_nonneg.mp h⟩⟩
    have hnotold : x ∉ frontier R :=
      fun h => disjoint_left.mp disjoint_interior_frontier hx.1.1 h
    refine ⟨hNiff, ?_⟩
    change x ∈ frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) ↔ f x = 0
    rw [hfront]
    simp only [mem_union, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff,
      hnotold, hxR, and_false, false_or, true_and]
    rw [← hqrep x hx.1, AddCircle.coe_eq_coe_iff_of_mem_Ico hsI haI,
      AddCircle.coe_eq_coe_iff_of_mem_Ico hsI hbI]
    exact ⟨fun h => sub_eq_zero.mpr (h.resolve_left hsa.ne').symm,
      fun h => Or.inr (sub_eq_zero.mp h).symm⟩
  refine ⟨f, U, hU, fun _ hx => hx.1.1, hfc.mono inter_subset_left, ?_, ?_, ?_,
    fun x hx => (hsign x hx).2, fun x hx => abs_lt.mpr hx.2, ?_⟩
  · intro i
    have hlocal := locallyPL_hamiltonZero_second_circle_coordinate e d hd phi hphi c i
    let ell : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ b - ContinuousAffineMap.id ℝ ℝ
    have h := (locallyPiecewiseAffineOn_affine ell isOpen_univ).comp hlocal
    rw [preimage_univ, inter_univ] at h
    have hUi : IsOpen ((e i).target ∩ (e i).symm ⁻¹' U) :=
      (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    exact (h.mono hUi (fun _ hx => ⟨hx.1, hx.2.1.2⟩)).congr (fun _ _ => rfl)
  · intro x hx
    rw [← hqrep x hx.1]
    change ((A.symm (q x) : ℝ) : C0) = (b : C0) - ((b - A.symm (q x) : ℝ) : C0)
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
  · intro x hx hxold hxb
    have hxint : x ∈ interior R := (mem_interior_iff_notMem_frontier hx.1).mpr hxold
    obtain ⟨t, ht, htq⟩ := hx.2
    have htA : t ∈ A.source := by
      change c < t ∧ t < c + p
      constructor <;> linarith [ht.1, ht.2]
    have hxW : x ∈ W := by
      refine ⟨hxint, ?_⟩
      change q x ∈ A.target
      rw [← htq]
      exact A.map_source htA
    have hft : f x = b - t := by
      change b - A.symm (q x) = b - t
      rw [← htq]
      exact congrArg (fun t : ℝ => b - t) (A.left_inv htA)
    have hta : a < t := lt_of_le_of_ne ht.1
      (fun h => hxb (htq.symm.trans (congrArg (fun t : ℝ => (t : C0)) h.symm)))
    refine ⟨hxW, ?_⟩
    change f x ∈ Ioo (-(b - a)) (b - a)
    rw [hft]
    constructor <;> linarith [ht.2]

end PoincareConjecture.M76
