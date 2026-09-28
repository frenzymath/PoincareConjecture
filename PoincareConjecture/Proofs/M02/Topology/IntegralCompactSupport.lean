import PoincareConjecture.Proofs.M02.Topology.IntegralFiniteSupport
import PoincareConjecture.Proofs.M02.Topology.IntegralConvexSupport
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportContinuity
import Mathlib.Topology.MetricSpace.Thickening









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Metric Set

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

theorem exists_finite_closedBall_support_neighborhood
    {X : Type u} [PseudoMetricSpace X]
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : Real, 0 < r ∧ ∃ s : Finset K,
      K ⊆ interior (⋃ x ∈ s, closedBall (x : X) r) ∧
      (⋃ x ∈ s, closedBall (x : X) r) ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : X) r)
    (fun _ => isOpen_ball) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hr⟩)
  refine ⟨r, hr, s, ?_, ?_⟩
  · apply hs.trans
    apply (isOpen_biUnion (fun x _ => isOpen_ball)).subset_interior_iff.mpr
    exact iUnion₂_mono (fun _ _ => ball_subset_closedBall)
  · exact iUnion₂_subset (fun x _ => (closedBall_subset_cthickening x.property r).trans hrU)

private theorem euclidean_compact_convex_above
    (K : Set (EuclideanSpace Real (Fin 3))) (hK : IsCompact K)
    (hc : Convex Real K) (n : Nat) :
    IsZero (integralSupportHomology K (n + 4)) := by
  rcases K.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]
    exact integralSupportHomology_empty_isZero (n + 4)
  · exact integralEuclideanCompactConvexSupportAbove_isZero K hK hc x hx n

private theorem euclidean_convex_intersection_above
    {ι : Type v} (s : Finset ι) (F : ι → Set (EuclideanSpace Real (Fin 3)))
    (hs : s.Nonempty) (hF : ∀ i ∈ s, IsCompact (F i))
    (hc : ∀ i ∈ s, Convex Real (F i)) (n : Nat) :
    IsZero (integralSupportHomology (⋂ i ∈ s, F i) (n + 4)) := by
  obtain ⟨j, hj⟩ := hs
  apply euclidean_compact_convex_above
  · exact (hF j hj).of_isClosed_subset
      (isClosed_iInter (fun i => isClosed_iInter (fun hi => (hF i hi).isClosed)))
      (fun x hx => mem_iInter.mp (mem_iInter.mp hx j) hj)
  · exact convex_iInter (fun i => convex_iInter (fun hi => hc i hi))

theorem integralEuclideanFiniteConvexSupportAbove_isZero
    {ι : Type v} (s : Finset ι) (F : ι → Set (EuclideanSpace Real (Fin 3)))
    (hF : ∀ i ∈ s, IsCompact (F i)) (hc : ∀ i ∈ s, Convex Real (F i)) (n : Nat) :
    IsZero (integralSupportHomology (⋃ i ∈ s, F i) (n + 4)) := by
  apply integralSupportHomology_finset_union_isZero s F 4 (fun i hi => (hF i hi).isClosed)
  intro t ht htn m
  exact euclidean_convex_intersection_above t F htn
    (fun i hi => hF i (ht hi)) (fun i hi => hc i (ht hi)) m

theorem integralEuclideanFiniteConvexSupportThree_detected
    {ι : Type v} (s : Finset ι) (F : ι → Set (EuclideanSpace Real (Fin 3)))
    (hF : ∀ i ∈ s, IsCompact (F i)) (hc : ∀ i ∈ s, Convex Real (F i))
    (a : integralSupportHomology (⋃ i ∈ s, F i) 3)
    (ha : ∀ x, ∀ hx : x ∈ ⋃ i ∈ s, F i,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3 a = 0) :
    a = 0 := by
  apply integralSupportHomology_finset_union_detected s F 3
    (fun i hi => (hF i hi).isClosed) ?_ ?_ a ha
  · intro t ht htn n
    exact euclidean_convex_intersection_above t F htn
      (fun i hi => hF i (ht hi)) (fun i hi => hc i (ht hi)) n
  · intro i hi b hb
    rcases (F i).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · have hz : IsZero (integralSupportHomology (F i) 3) := by
        rw [h]
        exact integralSupportHomology_empty_isZero 3
      exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _
    · let := integralCompactConvexSupportRestriction_homology_isIso
        (F i) (hF i hi) (hc i hi) x hx 3
      apply (ModuleCat.mono_iff_injective
        (integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3)).mp inferInstance
      rw [map_zero]
      exact hb x hx



theorem integralEuclideanCompactSupportAbove_isZero
    (K : Set (EuclideanSpace Real (Fin 3))) (hK : IsCompact K) (n : Nat) :
    IsZero (integralSupportHomology K (n + 4)) := by
  have hz : ∀ a : integralSupportHomology K (n + 4), a = 0 := by
    intro a
    obtain ⟨U, hU, hKU, hlift⟩ := exists_open_integralRelativeHomology_lift_forall K (n + 4) a
    obtain ⟨r, hr, s, hKs, hsU⟩ :=
      exists_finite_closedBall_support_neighborhood K U hK hU hKU
    let L := ⋃ x ∈ s, closedBall (x : EuclideanSpace Real (Fin 3)) r
    have hKL : K ⊆ L := hKs.trans interior_subset
    obtain ⟨b, hb⟩ := hlift L hKL hsU
    have hb₀ : b = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp
        (integralEuclideanFiniteConvexSupportAbove_isZero s
          (fun x : K => closedBall (x : EuclideanSpace Real (Fin 3)) r)
          (fun _ _ => isCompact_closedBall _ _) (fun _ _ => convex_closedBall _ _) n)).elim _ _
    rw [hb₀, map_zero] at hb
    exact hb.symm
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => (hz a).trans (hz b).symm⟩



theorem integralEuclideanCompactSupportThree_detected
    (K : Set (EuclideanSpace Real (Fin 3))) (hK : IsCompact K)
    (a : integralSupportHomology K 3)
    (ha : ∀ x, ∀ hx : x ∈ K,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3 a = 0) :
    a = 0 := by
  obtain ⟨U, hU, hKU, b, hb⟩ := exists_open_integralRelativeHomology_lift K 3 a
  change integralSupportHomologyRestriction hKU 3 b = a at hb
  have hlocal : ∀ x : K,
      integralSupportHomologyRestriction
        (singleton_subset_iff.mpr (hKU x.property)) 3 b = 0 := by
    intro x
    have he := congrArg (fun f => f b)
      (integralSupportHomologyRestriction_comp
        (singleton_subset_iff.mpr x.property) hKU 3)
    change integralSupportHomologyRestriction (singleton_subset_iff.mpr x.property) 3
        (integralSupportHomologyRestriction hKU 3 b) =
      integralSupportHomologyRestriction
        (singleton_subset_iff.mpr (hKU x.property)) 3 b at he
    rw [hb] at he
    exact he.symm.trans (ha x x.property)
  have hnear : ∀ x : K, ∃ V : Set (EuclideanSpace Real (Fin 3)),
      IsOpen V ∧ (x : EuclideanSpace Real (Fin 3)) ∈ V ∧
        integralSupportHomologyRestriction (inter_subset_left : U ∩ V ⊆ U) 3 b = 0 := by
    intro x
    exact exists_open_integralRelativeHomology_restriction_eq_zero
      U 3 b x (hKU x.property) (hlocal x)
  choose V hV hxV hbV using hnear
  let W := U ∩ ⋃ x : K, V x
  have hW : IsOpen W := hU.inter (isOpen_iUnion hV)
  have hKW : K ⊆ W := fun x hx => ⟨hKU hx, mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩⟩
  have hWlocal : ∀ y, ∀ hy : y ∈ W,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1) 3 b = 0 := by
    intro y hy
    obtain ⟨x, hyV⟩ := mem_iUnion.mp hy.2
    have hsmall : {y} ⊆ U ∩ V x := singleton_subset_iff.mpr ⟨hy.1, hyV⟩
    have he := congrArg (fun f => f b)
      (integralSupportHomologyRestriction_comp hsmall inter_subset_left 3)
    change integralSupportHomologyRestriction hsmall 3
        (integralSupportHomologyRestriction inter_subset_left 3 b) =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1) 3 b at he
    rw [hbV x, map_zero] at he
    exact he.symm
  obtain ⟨r, hr, s, hKs, hsW⟩ :=
    exists_finite_closedBall_support_neighborhood K W hK hW hKW
  let L := ⋃ x ∈ s, closedBall (x : EuclideanSpace Real (Fin 3)) r
  have hKL : K ⊆ L := hKs.trans interior_subset
  have hLU : L ⊆ U := hsW.trans inter_subset_left
  let c : integralSupportHomology L 3 := integralSupportHomologyRestriction hLU 3 b
  have hc : c = 0 := by
    apply integralEuclideanFiniteConvexSupportThree_detected s
      (fun x : K => closedBall (x : EuclideanSpace Real (Fin 3)) r)
      (fun _ _ => isCompact_closedBall _ _) (fun _ _ => convex_closedBall _ _)
    intro y hy
    have he := congrArg (fun f => f b)
      (integralSupportHomologyRestriction_comp (singleton_subset_iff.mpr hy) hLU 3)
    change integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr (hLU hy)) 3 b at he
    exact he.trans (hWlocal y (hsW hy))
  have hca : integralSupportHomologyRestriction hKL 3 c = a := by
    dsimp only [c]
    rw [← ConcreteCategory.comp_apply, integralSupportHomologyRestriction_comp]
    exact hb
  rw [hc, map_zero] at hca
  exact hca.symm

end PoincareConjecture.Proofs.M02.Topology
