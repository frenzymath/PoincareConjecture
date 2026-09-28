import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralFiniteSupport
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u v

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def IntegralSupportDetected (K : Set X) (d : Nat) : Prop :=
  ∀ a : integralSupportHomology K d,
    (∀ x : X, ∀ hx : x ∈ K,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = 0) → a = 0

theorem exists_finite_compact_support_refinement [T2Space X] [RegularSpace X]
    (K : Set X) (hK : IsCompact K) (U : K → Set X)
    (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x : K, (x : X) ∈ U x) :
    ∃ s : Finset K, ∃ F : K → Set X,
      (∀ x, IsCompact (F x) ∧ F x ⊆ K ∩ U x) ∧ (⋃ x ∈ s, F x) = K := by
  have hN : ∀ x : K, ∃ N : Set X,
      N ∈ nhds (x : X) ∧ IsClosed N ∧ N ⊆ U x :=
    fun x => exists_mem_nhds_isClosed_subset ((hU x).mem_nhds (hxU x))
  choose N hxN hNclosed hNU using hN
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (N x))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hxN ⟨x, hx⟩)⟩)
  refine ⟨s, fun x => K ∩ N x,
    (fun x => ⟨hK.inter_right (hNclosed x), inter_subset_inter_right K (hNU x)⟩), ?_⟩
  apply subset_antisymm (iUnion₂_subset (fun _ _ => inter_subset_left))
  intro y hy
  obtain ⟨x, hxs, hyN⟩ := mem_iUnion₂.mp (hs hy)
  exact mem_iUnion₂.mpr ⟨x, hxs, hy, interior_subset hyN⟩

theorem integralCompactSupport_local_to_global [T2Space X] [RegularSpace X]
    (K : Set X) (hK : IsCompact K) (d : Nat)
    (hlocal : ∀ x : X, x ∈ K → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ L : Set X, IsCompact L → L ⊆ U →
        (∀ n : Nat, IsZero (integralSupportHomology L (n + (d + 1)))) ∧
          IntegralSupportDetected L d) :
    (∀ n : Nat, IsZero (integralSupportHomology K (n + (d + 1)))) ∧
      IntegralSupportDetected K d := by
  classical
  choose U hU hxU hcalc using fun x : K => hlocal x x.property
  obtain ⟨s, F, hF, hFK⟩ := exists_finite_compact_support_refinement K hK U hU hxU
  have hclosed : ∀ x ∈ s, IsClosed (F x) := fun x _ => (hF x).1.isClosed
  have hI : ∀ t : Finset K, t ⊆ s → t.Nonempty → ∀ n : Nat,
      IsZero (integralSupportHomology (⋂ x ∈ t, F x) (n + (d + 1))) := by
    intro t ht htn n
    obtain ⟨x, hxt⟩ := htn
    have hcompact : IsCompact (⋂ y ∈ t, F y) :=
      (hF x).1.of_isClosed_subset
        (isClosed_iInter (fun y => isClosed_iInter (fun _ => (hF y).1.isClosed)))
        (fun z hz => mem_iInter.mp (mem_iInter.mp hz x) hxt)
    have hsub : (⋂ y ∈ t, F y) ⊆ U x := fun z hz =>
      ((hF x).2 (mem_iInter.mp (mem_iInter.mp hz x) hxt)).2
    exact (hcalc x _ hcompact hsub).1 n
  constructor
  · intro n
    simpa only [hFK] using
      integralSupportHomology_finset_union_isZero s F (d + 1) hclosed hI n
  · have hd : IntegralSupportDetected (⋃ x ∈ s, F x) d := by
      intro a ha
      apply integralSupportHomology_finset_union_detected s F d hclosed hI ?_ a ha
      intro x hx
      exact (hcalc x (F x) (hF x).1 (fun z hz => ((hF x).2 hz).2)).2
    simpa only [hFK] using hd

@[simp]
theorem integralSupportHomologyRestriction_apply_comp
    {K L D : Set X} (hKL : K ⊆ L) (hLD : L ⊆ D) (n : Nat)
    (a : integralSupportHomology D n) :
    integralSupportHomologyRestriction hKL n (integralSupportHomologyRestriction hLD n a) =
      integralSupportHomologyRestriction (hKL.trans hLD) n a :=
  congrArg (fun f => f a) (integralSupportHomologyRestriction_comp hKL hLD n)

theorem exists_integralSupportHomology_finite_gluing [T2Space X]
    (d : Nat) (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L d)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) d)
    {ι : Type v} (s : Finset ι) (F : ι → Set X)
    (hF : ∀ i ∈ s, IsCompact (F i))
    (hclasses : ∀ i ∈ s, ∃ a : integralSupportHomology (F i) d,
      ∀ x : X, ∀ hx : x ∈ F i,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x) :
    ∃ a : integralSupportHomology (⋃ i ∈ s, F i) d,
      ∀ x : X, ∀ hx : x ∈ ⋃ i ∈ s, F i,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro x hx
      simp at hx
  | @insert i s hi ih =>
      have hrest : ∀ j ∈ s, IsCompact (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      obtain ⟨b, hb⟩ := hclasses i (Finset.mem_insert_self i s)
      obtain ⟨c, hc⟩ := ih hrest (fun j hj => hclasses j (Finset.mem_insert_of_mem hj))
      let L := ⋃ j ∈ s, F j
      have hL : IsCompact L := s.isCompact_biUnion hrest
      have hcompat : integralSupportHomologyRestriction (inter_subset_left : F i ∩ L ⊆ F i) d b =
          integralSupportHomologyRestriction (inter_subset_right : F i ∩ L ⊆ L) d c := by
        apply sub_eq_zero.mp
        apply hD (F i ∩ L) ((hF i (Finset.mem_insert_self i s)).inter_right hL.isClosed)
        intro x hx
        rw [map_sub, integralSupportHomologyRestriction_apply_comp,
          integralSupportHomologyRestriction_apply_comp, hb x hx.1, hc x hx.2, sub_self]
      obtain ⟨a, hab, hac⟩ := exists_integralSupportHomology_union (F i) L
        (hF i (Finset.mem_insert_self i s)).isClosed hL.isClosed d b c hcompat
      rw [Finset.set_biUnion_insert]
      refine ⟨a, ?_⟩
      intro x hx
      rcases hx with hx | hx
      · have he := integralSupportHomologyRestriction_apply_comp
          (singleton_subset_iff.mpr hx) (subset_union_left : F i ⊆ F i ∪ L) d a
        rw [hab] at he
        exact he.symm.trans (hb x hx)
      · have he := integralSupportHomologyRestriction_apply_comp
          (singleton_subset_iff.mpr hx) (subset_union_right : L ⊆ F i ∪ L) d a
        rw [hac] at he
        exact he.symm.trans (hc x hx)

theorem exists_unique_integralSupportHomology_compact_gluing [T2Space X] [RegularSpace X]
    (d : Nat) (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L d)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) d)
    (K : Set X) (hK : IsCompact K)
    (hlocal : ∀ x : X, x ∈ K → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U d,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d b = omega y) :
    ∃! a : integralSupportHomology K d,
      ∀ x : X, ∀ hx : x ∈ K,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x := by
  classical
  choose U hU hxU b hb using fun x : K => hlocal x x.property
  obtain ⟨s, F, hF, hFK⟩ := exists_finite_compact_support_refinement K hK U hU hxU
  have hclasses : ∀ x ∈ s, ∃ a : integralSupportHomology (F x) d,
      ∀ y : X, ∀ hy : y ∈ F x,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d a = omega y := by
    intro x hx
    have hsub : F x ⊆ U x := fun y hy => ((hF x).2 hy).2
    refine ⟨integralSupportHomologyRestriction hsub d (b x), ?_⟩
    intro y hy
    rw [integralSupportHomologyRestriction_apply_comp]
    exact hb x y (hsub hy)
  have hex : ∃ a : integralSupportHomology K d,
      ∀ x : X, ∀ hx : x ∈ K,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x := by
    let P (L : Set X) : Prop := ∃ a : integralSupportHomology L d,
      ∀ x : X, ∀ hx : x ∈ L,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x
    have h : P (⋃ x ∈ s, F x) := exists_integralSupportHomology_finite_gluing d hD omega s F
      (fun x _ => (hF x).1) hclasses
    exact hFK ▸ h
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply sub_eq_zero.mp
  apply hD K hK
  intro x hx
  rw [map_sub, hb x hx, ha x hx, sub_self]

end Poincare.Topology
