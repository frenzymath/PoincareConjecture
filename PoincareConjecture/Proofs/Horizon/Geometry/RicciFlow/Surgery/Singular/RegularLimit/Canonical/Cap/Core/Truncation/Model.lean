import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.TruncatedDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.AxialShift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.NeckContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_metric_truncation_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
      ∀ b ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        ∃ E : OpenPartialHomeomorph M M,
          E.source = C.carrier ∧
          E.target = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target ∧
          (∀ x ∈ C.closed_core, E x = x) ∧
          ∀ x ∈ E.source, ∀ v : TangentSpace (𝓡 3) x,
            g.tangentNorm (E x) (mfderiv (𝓡 3) (𝓡 3) E x v) ≤
              (11 / 10 : ℝ) * g.tangentNorm x v := by
  classical
  obtain ⟨ε₁, hε₁, hsmall, hdisjoint⟩ :=
    exists_closed_core_disjoint_positive_end_closure_threshold.{u}
  obtain ⟨ε₂, hε₂, _, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε b hb
  let N := C.end_neck
  let L := C.epsilon⁻¹
  let l := (-L + b) / 2
  let δ := (b - l) / 2
  let U := C.closed_core ∪ N.region (-L) b
  have hL := inv_pos.mpr C.epsilon_pos
  have hl : -L < l := by dsimp [l, L]; linarith [hb.1]
  have hlb : l < b := by dsimp [l, L]; linarith [hb.1]
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlδ : l + δ < b := by dsimp [δ]; linarith
  have hNl : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hUopen : IsOpen U := by
    obtain ⟨_, _, hI, _, _, _⟩ := htrunc C (hε.trans (min_le_right _ _)) b hb
    change IsOpen (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)
    rw [← hI]
    exact isOpen_interior
  have hUsub : U ⊆ C.carrier :=
    union_subset C.closed_core_subset_carrier (fun _ hx => C.end_neck_subset hx.1)
  have hcoreOut {x : M} (hx : x ∈ C.closed_core) : x ∉ N.carrier := by
    rw [C.closed_core_eq_complement_end] at hx
    exact hx.2
  have hUend {x : M} (hx : x ∈ U) (hxN : x ∈ N.carrier) :
      x ∈ N.region (-L) b := hx.resolve_left (fun h => hcoreOut h hxN)
  obtain ⟨J, hJ, hJmono⟩ := CylinderGluing.exists_axial_expansion l hδ
    (show 0 ≤ L - b by dsimp [L]; linarith [hb.2])
  have hJfix (z : RoundCylinderSpace) (hz : z.2 ≤ l) : J z = z := by
    rw [hJ, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hδ.le)]
    simp only [mul_zero, add_zero, Prod.eta]
  have hJb (q : UnitTwoSphere) : J (q, b) = (q, L) := by
    rw [hJ, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδ).mpr (by linarith))]
    simp only [mul_one, add_sub_cancel]
  have hJifst (z : RoundCylinderSpace) : (J.symm z).1 = z.1 := by
    have hh := congrArg Prod.fst (J.apply_symm_apply z)
    simpa only [hJ] using hh
  have hJifix (z : RoundCylinderSpace) (hz : z.2 ≤ l) : J.symm z = z := by
    apply J.injective
    change J (J.symm z) = J z
    rw [J.apply_symm_apply, hJfix z hz]
  have hJinto (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-L) b) :
      J z ∈ N.cylinderDomain := by
    have hlo := hJmono z.1 hz.1
    have hhi := hJmono z.1 hz.2
    dsimp only at hlo hhi
    rw [hJfix (z.1, -L) hl.le] at hlo
    rw [hJb] at hhi
    change _ ∧ -N.epsilon⁻¹ < (J z).2 ∧ (J z).2 < N.epsilon⁻¹
    rw [hNl]
    exact ⟨mem_univ _, hlo, hhi⟩
  have hJifrom (z : RoundCylinderSpace) (hz : z ∈ N.cylinderDomain) :
      (J.symm z).2 ∈ Ioo (-L) b := by
    have hpair : (z.1, (J.symm z).2) = J.symm z := Prod.ext (hJifst z).symm rfl
    have hdom : z.2 ∈ Ioo (-L) L := by simpa only [hNl, L] using hz.2
    constructor
    · apply (hJmono z.1).lt_iff_lt.mp
      rw [hJfix (z.1, -L) hl.le, hpair, J.apply_symm_apply]
      exact hdom.1
    · apply (hJmono z.1).lt_iff_lt.mp
      rw [hpair, J.apply_symm_apply, hJb]
      exact hdom.2
  have hJiinto (z : RoundCylinderSpace) (hz : z ∈ N.cylinderDomain) :
      J.symm z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    rw [hNl]
    exact ⟨(hJifrom z hz).1, (hJifrom z hz).2.trans hb.2⟩
  let f : M → M := fun x => if x ∈ N.carrier then
    N.coordinate_map (J.symm (N.coordinate_inverse x)) else x
  let k : M → M := fun x => if x ∈ N.carrier then
    N.coordinate_map (J (N.coordinate_inverse x)) else x
  have hfon {x : M} (hx : x ∈ N.carrier) :
      f x = N.coordinate_map (J.symm (N.coordinate_inverse x)) := by
    simp only [f, if_pos hx]
  have hkon {x : M} (hx : x ∈ N.carrier) :
      k x = N.coordinate_map (J (N.coordinate_inverse x)) := by
    simp only [k, if_pos hx]
  have hfcore {x : M} (hx : x ∈ C.closed_core) : f x = x := by
    simp only [f, if_neg (hcoreOut hx)]
  have hkcore {x : M} (hx : x ∈ C.closed_core) : k x = x := by
    simp only [k, if_neg (hcoreOut hx)]
  have hfN {x : M} (hx : x ∈ N.carrier) :
      f x ∈ N.region (-L) b := by
    have hz := N.coordinate_inverse_mem x hx
    rw [hfon hx]
    refine ⟨N.coordinate_map_mem (hJiinto _ hz), ?_⟩
    rw [N.coordinate_inverse_coordinate_map (hJiinto _ hz)]
    exact hJifrom _ hz
  have hkN {x : M} (hx : x ∈ N.region (-L) b) : k x ∈ N.carrier := by
    rw [hkon hx.1]
    exact N.coordinate_map_mem (hJinto _ hx.2)
  have hfmap : MapsTo f C.carrier U := by
    intro x hx
    rcases C.carrier_eq_closed_core_union_end ▸ hx with hx | hx
    · rw [hfcore hx]
      exact Or.inl hx
    · exact Or.inr (hfN hx)
  have hkmap : MapsTo k U C.carrier := by
    rintro x (hx | hx)
    · rw [hkcore hx]
      exact C.closed_core_subset_carrier hx
    · exact C.end_neck_subset (hkN hx)
  have hkf : LeftInvOn k f C.carrier := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · have hz := N.coordinate_inverse_mem x hxN
      rw [hkon (hfN hxN).1, hfon hxN,
        N.coordinate_inverse_coordinate_map (hJiinto _ hz), J.apply_symm_apply,
        N.coordinate_map_coordinate_inverse hxN]
    · simp only [f, k, if_neg hxN]
  have hfk : LeftInvOn f k U := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · have hxR := hUend hx hxN
      rw [hfon (hkN hxR), hkon hxN,
        N.coordinate_inverse_coordinate_map (hJinto _ hxR.2), J.symm_apply_apply,
        N.coordinate_map_coordinate_inverse hxN]
    · simp only [f, k, if_neg hxN]
  let K := closure (N.region l L)
  have hcoreK : Disjoint C.closed_core K :=
    hdisjoint C (hε.trans (min_le_left _ _)) l ⟨hl, hlb.trans hb.2⟩
  have hlow {x : M} (hxN : x ∈ N.carrier) (hxK : x ∉ K) :
      (N.coordinate_inverse x).2 ≤ l := by
    apply le_of_not_gt
    intro hh
    apply hxK
    exact subset_closure ⟨hxN, hh,
      by simpa only [hNl, L] using (N.coordinate_inverse_mem x hxN).2.2⟩
  have hffix {x : M} (hx : x ∉ K) : f x = x := by
    by_cases hxN : x ∈ N.carrier
    · rw [hfon hxN, hJifix _ (hlow hxN hx), N.coordinate_map_coordinate_inverse hxN]
    · simp only [f, if_neg hxN]
  have hkfix {x : M} (hx : x ∉ K) : k x = x := by
    by_cases hxN : x ∈ N.carrier
    · rw [hkon hxN, hJfix _ (hlow hxN hx), N.coordinate_map_coordinate_inverse hxN]
    · simp only [k, if_neg hxN]
  have hfsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f C.carrier := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · have hi := N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hxN)
      have hm := N.coordinate_map_smooth.contMDiffAt
        (N.cylinderDomain_open.mem_nhds (hJiinto _ (N.coordinate_inverse_mem x hxN)))
      have heq : f =ᶠ[𝓝 x] N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse := by
        filter_upwards [N.carrier_open.mem_nhds hxN] with y hy
        simp only [f, if_pos hy, Function.comp_apply]
      exact ((hm.comp x (J.symm.contMDiff.contMDiffAt.comp x hi)).congr_of_eventuallyEq
        heq).contMDiffWithinAt
    · have hxcore : x ∈ C.closed_core :=
        (C.carrier_eq_closed_core_union_end ▸ hx).resolve_right hxN
      have hxK : x ∉ K := fun h => disjoint_left.mp hcoreK hxcore h
      have heq : f =ᶠ[𝓝 x] id := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxK] with y hy
        exact hffix hy
      exact (contMDiffAt_id.congr_of_eventuallyEq heq).contMDiffWithinAt
  have hksmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ k U := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · have hxR := hUend hx hxN
      have hi := N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hxN)
      have hm := N.coordinate_map_smooth.contMDiffAt
        (N.cylinderDomain_open.mem_nhds (hJinto _ hxR.2))
      have heq : k =ᶠ[𝓝 x] N.coordinate_map ∘ J ∘ N.coordinate_inverse := by
        filter_upwards [N.carrier_open.mem_nhds hxN] with y hy
        simp only [k, if_pos hy, Function.comp_apply]
      exact ((hm.comp x (J.contMDiff.contMDiffAt.comp x hi)).congr_of_eventuallyEq
        heq).contMDiffWithinAt
    · have hxcore : x ∈ C.closed_core := hx.resolve_right (fun h => hxN h.1)
      have hxK : x ∉ K := fun h => disjoint_left.mp hcoreK hxcore h
      have heq : k =ᶠ[𝓝 x] id := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxK] with y hy
        exact hkfix hy
      exact (contMDiffAt_id.congr_of_eventuallyEq heq).contMDiffWithinAt
  have hbound : ∀ x ∈ C.carrier, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        (11 / 10 : ℝ) * g.tangentNorm x v := by
    intro x hx v
    by_cases hxN : x ∈ N.carrier
    · have heq : f =ᶠ[𝓝 x] N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse := by
        filter_upwards [N.carrier_open.mem_nhds hxN] with y hy
        simp only [f, if_pos hy, Function.comp_apply]
      have hsmallN : N.epsilon ≤ 1 / 200 := by
        rw [hNl]
        exact (hε.trans (min_le_left _ _)).trans (hsmall.trans (by norm_num))
      have hh := N.tangentNorm_axial_compression_le hsmallN J l hδ
        (show 0 ≤ L - b by dsimp [L]; linarith [hb.2]) hJ hxN
        (hJiinto _ (N.coordinate_inverse_mem x hxN)) v
      dsimp only [TangentSpace] at hh ⊢
      rw [heq.eq_of_nhds, heq.mfderiv_eq]
      exact hh
    · have hxcore : x ∈ C.closed_core :=
        (C.carrier_eq_closed_core_union_end ▸ hx).resolve_right hxN
      have hxK : x ∉ K := fun h => disjoint_left.mp hcoreK hxcore h
      have heq : f =ᶠ[𝓝 x] id := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxK] with y hy
        exact hffix hy
      dsimp only [TangentSpace]
      rw [heq.eq_of_nhds, heq.mfderiv_eq, mfderiv_id]
      change g.tangentNorm x v ≤ (11 / 10 : ℝ) * g.tangentNorm x v
      have hn : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
      linarith
  let E : OpenPartialHomeomorph M M := {
    toFun := f
    invFun := k
    source := C.carrier
    target := U
    map_source' := hfmap
    map_target' := hkmap
    left_inv' := hkf
    right_inv' := hfk
    open_source := C.carrier_open
    open_target := hUopen
    continuousOn_toFun := hfsmooth.continuousOn
    continuousOn_invFun := hksmooth.continuousOn }
  exact ⟨E, rfl, rfl, hfsmooth, hksmooth, fun _ hx => hfcore hx, hbound⟩

theorem exists_smooth_truncation_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
      ∀ b ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        ∃ E : OpenPartialHomeomorph M M,
          E.source = C.carrier ∧
          E.target = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target ∧
          ∀ x ∈ C.closed_core, E x = x := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := exists_metric_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε b hb
  obtain ⟨E, hsource, htarget, hE, hEi, hfix, _⟩ := htransport C hε b hb
  exact ⟨E, hsource, htarget, hE, hEi, hfix⟩

theorem exists_truncated_carrier_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
      ∀ b ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        Nonempty (CapModelEquivalence C.model_kind C.puncture
          (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)) := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := exists_smooth_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε b hb
  obtain ⟨E, hsource, htarget, hE, hEi, _⟩ := htransport C hε b hb
  have hmodel := C.imageModelEquivalence E (by rw [hsource]) hE hEi
  have heq : E '' C.carrier = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b := by
    rw [← hsource, E.image_source_eq_target, htarget]
  exact ⟨heq ▸ hmodel⟩

end PoincareConjecture.CapCertificate
