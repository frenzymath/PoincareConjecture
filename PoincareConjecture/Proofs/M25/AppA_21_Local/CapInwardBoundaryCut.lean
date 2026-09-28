import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBoundaryOrientation
import PoincareConjecture.Proofs.M25.AppA_21_Local.Opposite

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.inward_boundary_slice_compact_component
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) (R : EpsilonNeck g)
    (hR : R = C.boundary_neck ∨ R = C.boundary_neck.reverse)
    (hcore : R.carrier ∩ C.core = R.region (-C.epsilon⁻¹) 0)
    {t : ℝ} (ht : t ∈ Ioo (-C.epsilon⁻¹) 0) :
    let L := C.epsilon⁻¹
    let q := (R.coordinate_inverse R.center).1
    let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, t))
    let a := R.coordinate_map (q, (t - L) / 2)
    let b := R.coordinate_map (q, t / 2)
    let A := connectedComponentIn Sᶜ a
    let B := connectedComponentIn Sᶜ b
    C.closed_core \ R.region t L = closure A ∧
      IsCompact (closure A) ∧ closure A ⊆ C.core ∧
      a ∉ S ∧ b ∉ S ∧ A ≠ B ∧
      frontier A = S ∧ frontier B = S ∧
      R.region (-L) t ⊆ A ∧ R.region t L ⊆ B ∧
      A ∪ S ∪ B = connectedComponent R.center := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := C.epsilon⁻¹
  let q := (R.coordinate_inverse R.center).1
  let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, t))
  let a := R.coordinate_map (q, (t - L) / 2)
  let b := R.coordinate_map (q, t / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  let K := C.closed_core \ R.region t L
  change K = closure A ∧ IsCompact (closure A) ∧ closure A ⊆ C.core ∧
    a ∉ S ∧ b ∉ S ∧ A ≠ B ∧ frontier A = S ∧ frontier B = S ∧
    R.region (-L) t ⊆ A ∧ R.region t L ⊆ B ∧
    A ∪ S ∪ B = connectedComponent R.center
  change -L < t ∧ t < 0 at ht
  change R.carrier ∩ C.core = R.region (-L) 0 at hcore
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hepsilon : R.epsilon = C.epsilon := by
    rcases hR with rfl | rfl <;> exact C.boundary_neck_epsilon
  have hRsub : R.carrier ⊆ C.carrier := by
    rcases hR with rfl | rfl <;> exact C.boundary_neck_subset
  have hRsphere : R.central_sphere = C.boundary_sphere := by
    rcases hR with rfl | rfl <;> exact C.boundary_eq_neck_sphere.symm
  have htR : t ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
    rw [hepsilon]
    exact ⟨ht.1, ht.2.trans hL⟩
  have hcoreOpen : IsOpen C.core := by
    rw [C.core_eq_interior_closed_core]
    exact isOpen_interior
  have hcoreK : C.core ⊆ C.closed_core := by
    rw [C.core_eq_interior_closed_core]
    exact interior_subset
  have hKcompact : IsCompact K :=
    C.closed_core_compact.diff (R.isOpen_region t L)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKcore : K ⊆ C.core := by
    intro x hx
    by_contra hxcore
    have hxfront : x ∈ frontier C.closed_core := by
      refine ⟨subset_closure hx.1, ?_⟩
      intro hxint
      exact hxcore (C.core_eq_interior_closed_core.symm ▸ hxint)
    rw [C.core_frontier_eq_boundary, ← hRsphere] at hxfront
    obtain ⟨hxR, hxzero⟩ := (R.mem_central_sphere_iff x).mp hxfront
    apply hx.2
    refine ⟨hxR, ?_⟩
    rw [hxzero]
    exact ⟨ht.2, hL⟩
  have hSmem (x : M) : x ∈ S ↔
      x ∈ R.carrier ∧ (R.coordinate_inverse x).2 = t := by
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨R.coordinate_map_mem ⟨mem_univ _, htR⟩, ?_⟩
      rw [R.coordinate_inverse_map (v, t) htR]
    · rintro ⟨hxR, hxt⟩
      refine ⟨(R.coordinate_inverse x).1, ?_⟩
      have hz : ((R.coordinate_inverse x).1, t) = R.coordinate_inverse x :=
        Prod.ext rfl hxt.symm
      change R.coordinate_map ((R.coordinate_inverse x).1, t) = x
      rw [hz]
      exact R.coordinate_map_inverse hxR

  let E := R.coordinate_map '' (univ ×ˢ Icc t (0 : ℝ))
  have hEcompact : IsCompact E := R.isCompact_coordinate_slab
    (by rw [hepsilon]; exact ht.1) (by rw [hepsilon]; exact hL)
  have hcorePositive : C.core ∩ R.region t L ⊆ E := by
    intro x hx
    have hxnegative : x ∈ R.region (-L) 0 := hcore ▸ ⟨hx.2.1, hx.1⟩
    exact ⟨R.coordinate_inverse x,
      ⟨mem_univ _, hx.2.2.1.le, hxnegative.2.2.le⟩,
      R.coordinate_map_inverse hx.2.1⟩
  have houtside : C.core ∩ Eᶜ ⊆ K := by
    intro x hx
    exact ⟨hcoreK hx.1, fun hxpositive => hx.2 (hcorePositive ⟨hx.1, hxpositive⟩)⟩
  have houtsideOpen : IsOpen (C.core ∩ Eᶜ) :=
    hcoreOpen.inter hEcompact.isClosed.isOpen_compl
  have hKfront : frontier K ⊆ S := by
    intro x hx
    have hxK : x ∈ K := hKclosed.frontier_subset hx
    have hxE : x ∈ E := by
      by_contra hxout
      exact hx.2 (interior_maximal houtside houtsideOpen ⟨hKcore hxK, hxout⟩)
    rcases hxE with ⟨z, hz, rfl⟩
    have hzdom : z.2 ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
      rw [hepsilon]
      exact ⟨ht.1.trans_le hz.2.1, hz.2.2.trans_lt hL⟩
    have hzt : z.2 = t := by
      apply le_antisymm ?_ hz.2.1
      apply le_of_not_gt
      intro htz
      apply hxK.2
      refine ⟨R.coordinate_map_mem ⟨mem_univ _, hzdom⟩, ?_⟩
      rw [R.coordinate_inverse_map z hzdom]
      exact ⟨htz, hz.2.2.trans_lt hL⟩
    exact ⟨z.1, congrArg R.coordinate_map (Prod.ext rfl hzt.symm)⟩
  have hconnected {c d : ℝ} (hc : -L ≤ c) (hd : d ≤ L) (hcd : c < d) :
      IsConnected (R.region c d) := by
    have hdom (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo c d) :
        z ∈ R.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      rw [hepsilon]
      exact ⟨hc.trans_lt hz.2.1, hz.2.2.trans_le hd⟩
    have heq : R.region c d = R.coordinate_map '' (univ ×ˢ Ioo c d) := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨R.coordinate_inverse x, ⟨mem_univ _, hx.2⟩,
          R.coordinate_map_inverse hx.1⟩
      · rintro x ⟨z, hz, rfl⟩
        refine ⟨R.coordinate_map_mem (hdom z hz), ?_⟩
        rw [R.coordinate_inverse_coordinate_map (hdom z hz)]
        exact hz.2
    rw [heq]
    apply (isConnected_univ.prod (isConnected_Ioo hcd)).image
    exact R.coordinate_map_smooth.continuousOn.mono (fun z hz => hdom z hz)
  have hminusConnected : IsConnected (R.region (-L) t) :=
    hconnected le_rfl (ht.2.trans hL).le ht.1
  have hplusConnected : IsConnected (R.region t L) :=
    hconnected ht.1.le le_rfl (ht.2.trans hL)
  have hminusAvoid : R.region (-L) t ⊆ Sᶜ := by
    intro x hx hxS
    exact hx.2.2.ne ((hSmem x).mp hxS).2
  have hplusAvoid : R.region t L ⊆ Sᶜ := by
    intro x hx hxS
    exact hx.2.1.ne' ((hSmem x).mp hxS).2
  have haDom : (t - L) / 2 ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
    rw [hepsilon]
    change -L < (t - L) / 2 ∧ (t - L) / 2 < L
    constructor <;> linarith only [ht.1, ht.2, hL]
  have hbDom : t / 2 ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
    rw [hepsilon]
    change -L < t / 2 ∧ t / 2 < L
    constructor <;> linarith only [ht.1, ht.2, hL]
  have haMinus : a ∈ R.region (-L) t := by
    change R.coordinate_map (q, (t - L) / 2) ∈ R.region (-L) t
    refine ⟨R.coordinate_map_mem ⟨mem_univ _, haDom⟩, ?_⟩
    rw [R.coordinate_inverse_map (q, (t - L) / 2) haDom]
    change -L < (t - L) / 2 ∧ (t - L) / 2 < t
    constructor <;> linarith only [ht.1, ht.2, hL]
  have hbPlus : b ∈ R.region t L := by
    change R.coordinate_map (q, t / 2) ∈ R.region t L
    refine ⟨R.coordinate_map_mem ⟨mem_univ _, hbDom⟩, ?_⟩
    rw [R.coordinate_inverse_map (q, t / 2) hbDom]
    change t < t / 2 ∧ t / 2 < L
    constructor <;> linarith only [ht.1, ht.2, hL]
  have haS : a ∉ S := hminusAvoid haMinus
  have hbS : b ∉ S := hplusAvoid hbPlus
  have hminusA : R.region (-L) t ⊆ A :=
    hminusConnected.isPreconnected.subset_connectedComponentIn haMinus hminusAvoid
  have hplusB : R.region t L ⊆ B :=
    hplusConnected.isPreconnected.subset_connectedComponentIn hbPlus hplusAvoid
  have hminusK : R.region (-L) t ⊆ K := by
    intro x hx
    have hxnegative : x ∈ R.region (-L) 0 :=
      ⟨hx.1, hx.2.1, hx.2.2.trans ht.2⟩
    have hxcore : x ∈ C.core := (hcore.symm ▸ hxnegative).2
    exact ⟨hcoreK hxcore, fun hxpositive => lt_asymm hx.2.2 hxpositive.2.1⟩
  have hAsub : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hBsub : B ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hApre : IsPreconnected A := isPreconnected_connectedComponentIn
  have hBpre : IsPreconnected B := isPreconnected_connectedComponentIn
  have hAinside : A ⊆ interior K := by
    apply hApre.subset_of_closure_inter_subset isOpen_interior
      ⟨a, hminusA haMinus, interior_maximal hminusK (R.isOpen_region (-L) t) haMinus⟩
    intro x hx
    by_contra hxint
    have hxK : x ∈ K := (closure_minimal interior_subset hKclosed) hx.1
    exact hAsub hx.2 (hKfront ⟨subset_closure hxK, hxint⟩)
  have hBoutside : B ⊆ Kᶜ := by
    apply hBpre.subset_of_closure_inter_subset hKclosed.isOpen_compl
      ⟨b, hplusB hbPlus, fun hbK => hbK.2 hbPlus⟩
    intro x hx hxK
    have hxnotint : x ∉ interior K := by
      intro hxint
      obtain ⟨y, hyint, hyout⟩ := mem_closure_iff.mp hx.1
        (interior K) isOpen_interior hxint
      exact hyout (interior_subset hyint)
    exact hBsub hx.2 (hKfront ⟨subset_closure hxK, hxnotint⟩)
  have hne : A ≠ B := by
    intro hAB
    have hbA : b ∈ A := hAB.symm ▸ hplusB hbPlus
    exact hBoutside (hplusB hbPlus) (interior_subset (hAinside hbA))
  have hsliceClosure {c d : ℝ} (hc : -L ≤ c) (hd : d ≤ L)
      (hcd : c < d) (htcd : t ∈ Icc c d) : S ⊆ closure (R.region c d) := by
    rintro x ⟨v, rfl⟩
    have hline : ContinuousAt (fun s : ℝ => R.coordinate_map (v, s)) t :=
      (R.coordinate_map_smooth.continuousOn.continuousAt
        (R.cylinderDomain_open.mem_nhds ⟨mem_univ _, htR⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt
    have hwithin : ContinuousWithinAt (fun s : ℝ => R.coordinate_map (v, s))
        (Ioo c d) t := hline.continuousWithinAt
    apply hwithin.mem_closure
    · rw [closure_Ioo hcd.ne]
      exact htcd
    · intro s hs
      have hsdom : s ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
        rw [hepsilon]
        exact ⟨hc.trans_lt hs.1, hs.2.trans_le hd⟩
      refine ⟨R.coordinate_map_mem ⟨mem_univ _, hsdom⟩, ?_⟩
      rw [R.coordinate_inverse_map (v, s) hsdom]
      exact hs
  have hSclMinus : S ⊆ closure (R.region (-L) t) :=
    hsliceClosure le_rfl (ht.2.trans hL).le ht.1 ⟨ht.1.le, le_rfl⟩
  have hSclPlus : S ⊆ closure (R.region t L) :=
    hsliceClosure ht.1.le le_rfl (ht.2.trans hL) ⟨le_rfl, (ht.2.trans hL).le⟩
  have hSfront : S ⊆ frontier A ∩ frontier B := by
    intro x hxS
    exact ⟨⟨closure_mono hminusA (hSclMinus hxS),
      fun hxint => hAsub (interior_subset hxint) hxS⟩,
      ⟨closure_mono hplusB (hSclPlus hxS),
        fun hxint => hBsub (interior_subset hxint) hxS⟩⟩
  obtain ⟨hfrontA, hfrontB, _, _, hcoverA⟩ :=
    R.opposite_level_components htR a b haS hbS hne hSfront
  have hcomponent : connectedComponent a = connectedComponent R.center := by
    apply (connectedComponent_eq ?_).symm
    exact R.isConnected_carrier.subset_connectedComponent
      (R.central_sphere_subset R.center_on_central_sphere) haMinus.1
  have hcover : A ∪ S ∪ B = connectedComponent R.center := hcoverA.trans hcomponent
  have hcapComponent : C.carrier ⊆ connectedComponent R.center :=
    C.m25_isConnected_carrier.subset_connectedComponent
      (hRsub (R.central_sphere_subset R.center_on_central_sphere))
  have hclosureAK : closure A ⊆ K :=
    closure_minimal (hAinside.trans interior_subset) hKclosed
  have hKclosureA : K ⊆ closure A := by
    intro x hx
    have hxcover := hcapComponent (C.m25_core_subset_carrier (hKcore hx))
    rw [← hcover] at hxcover
    rcases hxcover with (hxA | hxS) | hxB
    · exact subset_closure hxA
    · exact closure_mono hminusA (hSclMinus hxS)
    · exact (hBoutside hxB hx).elim
  have heq : K = closure A := Subset.antisymm hKclosureA hclosureAK
  refine ⟨heq, ?_, ?_, haS, hbS, hne, hfrontA, hfrontB, hminusA, hplusB, hcover⟩
  · rw [← heq]
    exact hKcompact
  · rw [← heq]
    exact hKcore

end PoincareConjecture
