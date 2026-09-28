import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.InteriorPhaseCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.SourceSlab
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleSlab
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_shifted_lower_slab_coordinate
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    ∃ (f : X → ℝ) (U : Set X), IsOpen U ∧ U ⊆ interior R ∧ ContinuousOn f U ∧
      (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' U)) ∧
      (∀ x ∈ U, ambientSourcePhase phi x = (a : C) + (f x : C)) ∧
      (∀ x ∈ U, x ∈ interior (sourceSlab phi a b) ↔ 0 < f x) ∧
      (∀ x ∈ U, x ∈ frontier (sourceSlab phi a b) ↔ f x = 0) ∧
      (∀ x ∈ U, |f x| < b - a) ∧
      ∀ x ∈ sourceSlab phi a b, x ∉ frontier R →
        ambientSourcePhase phi x ≠ (b : C) → x ∈ U := by
  let q := ambientSourcePhase phi
  let A := AddCircle.openPartialHomeomorphCoe p c
  let W := interior R ∩ q ⁻¹' A.target
  let f := fun x => A.symm (q x) - a
  have hW : IsOpen W :=
    ((continuousOn_ambientSourcePhase phi).mono interior_subset).isOpen_inter_preimage
      isOpen_interior A.open_target
  have hfc : ContinuousOn f W :=
    (A.symm.continuousOn.comp ((continuousOn_ambientSourcePhase phi).mono
      (inter_subset_left.trans interior_subset)) (fun _ hx => hx.2)).sub continuousOn_const
  let U := W ∩ f ⁻¹' Ioo (-(b - a)) (b - a)
  have hU : IsOpen U := hfc.isOpen_inter_preimage hW isOpen_Ioo
  have hrep (x : X) (hx : x ∈ W) : A.symm (q x) ∈ Ioo c (c + p) := by
    simpa only [A, AddCircle.openPartialHomeomorphCoe_source] using A.map_target hx.2
  have hqrep (x : X) (hx : x ∈ W) : ((A.symm (q x) : ℝ) : C) = q x := A.right_inv hx.2
  have haI : a ∈ Ico c (c + p) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico c (c + p) := ⟨by linarith, by linarith⟩
  have hsign (x : X) (hx : x ∈ U) :
      (x ∈ sourceSlab phi a b ↔ 0 ≤ f x) ∧
      (x ∈ frontier (sourceSlab phi a b) ↔ f x = 0) := by
    let xR : R := ⟨x, interior_subset hx.1.1⟩
    have hs := hrep x hx.1
    have hsI : A.symm (q x) ∈ Ico c (c + p) := ⟨hs.1.le, by linarith [hs.2]⟩
    have hsb : A.symm (q x) < b := by
      have h := hx.2.2
      change A.symm (q x) - a < b - a at h
      linarith
    have hmem : x ∈ sourceSlab phi a b ↔ q x ∈ AddCircle.closedIntervalArc p a b :=
      (mem_sourceSlab_iff phi a b xR).trans (by rw [← ambientSourcePhase_domain phi xR])
    have hRiff : x ∈ sourceSlab phi a b ↔ 0 ≤ f x := by
      rw [hmem, ← hqrep x hx.1,
        (AddCircle.coe_mem_closedIntervalArc_shifted_iff p) ha.le hb ⟨hs.1.le, hs.2⟩]
      exact ⟨fun h => sub_nonneg.mpr h.1, fun h => ⟨sub_nonneg.mp h, hsb.le⟩⟩
    have hnotold : x ∉ frontier R :=
      fun h => disjoint_left.mp disjoint_interior_frontier hx.1.1 h
    have hsurface (t : C) : x ∈ sourceSurface phi t ↔ q x = t :=
      (mem_sourceSurface_iff phi t xR).trans (by rw [← ambientSourcePhase_domain phi xR])
    refine ⟨hRiff, ?_⟩
    rw [hfront]
    change ((x ∈ sourceSlab phi a b ∧ x ∈ frontier R) ∨
      x ∈ sourceSurface phi (a : C) ∨ x ∈ sourceSurface phi (b : C)) ↔ f x = 0
    simp only [hnotold, and_false, false_or, hsurface]
    rw [← hqrep x hx.1, AddCircle.coe_eq_coe_iff_of_mem_Ico hsI haI,
      AddCircle.coe_eq_coe_iff_of_mem_Ico hsI hbI]
    exact ⟨fun h => sub_eq_zero.mpr (h.resolve_right hsb.ne),
      fun h => Or.inl (sub_eq_zero.mp h)⟩
  refine ⟨f, U, hU, fun _ hx => hx.1.1, hfc.mono inter_subset_left, ?_, ?_, ?_,
    fun x hx => (hsign x hx).2, fun x hx => abs_lt.mpr hx.2, ?_⟩
  · intro i
    have hlocal := locallyPL_interior_circle_coordinate e d hd phi hphi c i
    let ell : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ a
    have h := (locallyPiecewiseAffineOn_affine ell isOpen_univ).comp hlocal
    rw [preimage_univ, inter_univ] at h
    have hUi : IsOpen ((e i).target ∩ (e i).symm ⁻¹' U) :=
      (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    exact (h.mono hUi (fun _ hx => ⟨hx.1, hx.2.1⟩)).congr (fun _ _ => rfl)
  · intro x hx
    change q x = (a : C) + (f x : C)
    rw [← hqrep x hx.1]
    change ((A.symm (q x) : ℝ) : C) = (a : C) + ((A.symm (q x) - a : ℝ) : C)
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
    let xR : R := ⟨x, sourceSlab_subset phi a b hx⟩
    have hxint : x ∈ interior R := (mem_interior_iff_notMem_frontier xR.property).mpr hxold
    obtain ⟨t, ht, htq⟩ := (mem_sourceSlab_iff phi a b xR).mp hx
    have htq' : (t : C) = q x := htq.trans (ambientSourcePhase_domain phi xR).symm
    have htA : t ∈ A.source := by
      change c < t ∧ t < c + p
      constructor <;> linarith [ht.1, ht.2]
    have hxW : x ∈ W := by
      refine ⟨hxint, ?_⟩
      change q x ∈ A.target
      rw [← htq']
      exact A.map_source htA
    have hft : f x = t - a := by
      change A.symm (q x) - a = t - a
      rw [← htq']
      exact congrArg (fun t : ℝ => t - a) (A.left_inv htA)
    have htb : t < b := lt_of_le_of_ne ht.2
      (fun h => hxb (htq'.symm.trans (congrArg (fun t : ℝ => (t : C)) h)))
    refine ⟨hxW, ?_⟩
    change f x ∈ Ioo (-(b - a)) (b - a)
    rw [hft]
    constructor <;> linarith [ht.1]

theorem exists_lower_slab_coordinate
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    ∃ (f : X → ℝ) (U : Set X), IsOpen U ∧ U ⊆ interior R ∧ ContinuousOn f U ∧
      (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' U)) ∧
      (∀ x ∈ U, ambientSourcePhase phi x = (a : C) + (f x : C)) ∧
      (∀ x ∈ U, x ∈ interior (sourceSlab phi a b) ↔ 0 < f x) ∧
      (∀ x ∈ U, x ∈ frontier (sourceSlab phi a b) ↔ f x = 0) ∧
      (∀ x ∈ U, |f x| < b - a) ∧
      ∀ x ∈ sourceSlab phi a b, x ∉ frontier R →
        ambientSourcePhase phi x ≠ (b : C) → x ∈ U := by
  exact exists_shifted_lower_slab_coordinate e d hd phi hphi ha hab (by simpa using hb) hfront

end PoincareConjecture.M76.HamiltonIntervalTorus
