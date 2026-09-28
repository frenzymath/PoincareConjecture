import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CapStandardEnd
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBasics
import PoincareConjecture.Definitions.Ch09.NeckCapTopology









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D







structure ClosedModelCapData
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  carrier : Set M
  carrier_open : IsOpen carrier
  puncture : RealProjectiveThree
  model_kind : CapModelKind
  model_equivalence : CapModelEquivalence model_kind puncture carrier
  end_chart : OpenPartialHomeomorph RoundCylinderSpace M
  end_chart_source :
    end_chart.source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  end_chart_target_subset : end_chart.target ⊆ carrier
  end_chart_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      end_chart end_chart.source
  end_chart_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      end_chart.symm end_chart.target
  closed_core : Set M
  closed_core_compact : IsCompact closed_core
  closed_core_eq_complement_end :
    closed_core = carrier \ end_chart.target
  compact_tail_complement : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
    IsCompact (carrier \ end_chart.cylinderTail epsilon⁻¹ s)
  cut_topology : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
    let T := end_chart.cylinderTail epsilon⁻¹ s
    let K := carrier \ T
    let V := closed_core ∪ end_chart '' (univ ×ˢ Ioo (-epsilon⁻¹) s)
    let S := end_chart '' (univ ×ˢ ({s} : Set ℝ))
    K ⊆ carrier ∧ IsOpen V ∧ closure V = K ∧ interior K = V ∧
      frontier V = S ∧ frontier K = S ∧ frontier carrier ⊆ closure T
  core : Set M
  core_nonempty : core.Nonempty
  core_subset_closed_core : core ⊆ closed_core
  carrier_connected : IsConnected carrier


noncomputable def ClosedModelCapData.ofCapCertificate
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) : ClosedModelCapData g := by
  let e : OpenPartialHomeomorph RoundCylinderSpace M :=
    C.end_neck.coordinatePartialHomeomorph
  let L := C.epsilon⁻¹
  have hsource : e.source = univ ×ˢ Ioo (-L) L := by
    change C.end_neck.cylinderDomain = _
    simp only [L, EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
  have htarget : e.target = C.end_neck.carrier := by
    rfl
  have hregion (a b : ℝ) (ha : -L ≤ a) (hb : b ≤ L) (hab : a < b) :
      e '' (univ ×ˢ Ioo a b) = C.end_neck.region a b := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzs : z.2 ∈ Ioo (-L) L :=
        ⟨ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
      refine ⟨e.map_source (hsource.symm ▸ ⟨mem_univ _, hzs⟩), ?_⟩
      change (e.symm (e z)).2 ∈ Ioo a b
      rw [e.left_inv (hsource.symm ▸ ⟨mem_univ _, hzs⟩)]
      exact hz.2
    · intro hx
      have hxN : x ∈ e.target := htarget.symm ▸ hx.1
      refine ⟨e.symm x, ?_, e.right_inv hxN⟩
      refine ⟨mem_univ _, ?_⟩
      change a < (e.symm x).2 ∧ (e.symm x).2 < b
      simpa only [e, EpsilonNeck.coordinatePartialHomeomorph_symm_apply] using hx.2
  have htail (s : ℝ) (hs : s ∈ Ioo (-L) L) :
      e.cylinderTail L s = C.end_neck.region s L := by
    ext x
    rw [e.mem_cylinderTail_iff hsource hs.1 x]
    constructor
    · rintro ⟨hx, hheight⟩
      refine ⟨htarget ▸ hx, ?_⟩
      simpa only [e, EpsilonNeck.coordinatePartialHomeomorph_symm_apply,
        mem_Ioo] using hheight
    · rintro ⟨hx, hheight⟩
      refine ⟨htarget.symm ▸ hx, ?_⟩
      change (e.symm x).2 ∈ Ioo s L
      simpa only [e, EpsilonNeck.coordinatePartialHomeomorph_symm_apply,
        mem_Ioo] using hheight
  exact
    { epsilon := C.epsilon
      epsilon_pos := C.epsilon_pos
      carrier := C.carrier
      carrier_open := C.carrier_open
      puncture := C.puncture
      model_kind := C.model_kind
      model_equivalence := C.model_equivalence
      end_chart := e
      end_chart_source := by simpa only [L] using hsource
      end_chart_target_subset := by
        rw [htarget]
        exact C.end_neck_subset
      end_chart_smooth := by
        change ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
          C.end_neck.coordinate_map e.source
        rw [hsource]
        simpa only [L, C.end_neck_epsilon] using C.end_neck.coordinate_map_smooth
      end_chart_inverse_smooth := by
        change ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
          C.end_neck.coordinate_inverse e.target
        rw [htarget]
        exact C.end_neck.coordinate_inverse_smooth
      closed_core := C.closed_core
      closed_core_compact := C.closed_core_compact
      closed_core_eq_complement_end := by
        simpa only [htarget] using C.closed_core_eq_complement_end
      compact_tail_complement := by
        intro s hs
        have hs' : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by simpa only [L] using hs
        simpa only [htail s hs, L] using C.isCompact_end_neck_lower_cut hs'
      cut_topology := by
        intro s hs
        have hs' : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by simpa only [L] using hs
        have hcut := C.end_neck_lower_cut_topology hs'
        have hlow := hregion (-L) s (le_rfl) hs.2.le hs.1
        have hupper := htail s hs
        have hslice : e '' (univ ×ˢ ({s} : Set ℝ)) =
            C.end_neck.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) := by
          rfl
        simpa only [L, hupper, hlow, hslice] using hcut
      core := C.core
      core_nonempty := C.core_nonempty
      core_subset_closed_core := by
        rw [C.core_eq_interior_closed_core]
        exact interior_subset
      carrier_connected := by
        have hcore : C.core ⊆ C.carrier := by
          rw [C.core_eq_interior_closed_core]
          exact interior_subset.trans (by
            rw [C.closed_core_eq_complement_end]
            exact sdiff_subset)
        refine ⟨C.core_nonempty.mono hcore, isPreconnected_of_forall_pair ?_⟩
        intro x hx y hy
        have hle : intrinsicEDist g C.carrier x y ≤
            intrinsicDiameter g C.carrier :=
          le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
        have hdist : intrinsicEDist g C.carrier x y < ⊤ :=
          hle.trans_lt (lt_trans C.intrinsic_diameter_bound ENNReal.ofReal_lt_top)
        obtain ⟨L, ⟨γ, hγ, h0, h1, hsub, _⟩, _⟩ := sInf_lt_iff.mp hdist
        refine ⟨γ '' Icc (0 : ℝ) 1, hsub, ?_, ?_,
          isPreconnected_Icc.image γ hγ.continuousOn⟩
        · exact ⟨0, by norm_num, h0⟩
        · exact ⟨1, by norm_num, h1⟩ }

theorem ClosedModelCapData.ofCapCertificate_end_chart_tail
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) {s : ℝ}
    (hs : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    (ClosedModelCapData.ofCapCertificate C).end_chart.cylinderTail
        C.epsilon⁻¹ s = C.end_neck.region s C.epsilon⁻¹ := by
  classical
  change C.end_neck.coordinatePartialHomeomorph.cylinderTail
      C.epsilon⁻¹ s = C.end_neck.region s C.epsilon⁻¹
  ext x
  rw [C.end_neck.coordinatePartialHomeomorph.mem_cylinderTail_iff
    (by
      change C.end_neck.cylinderDomain = _
      simp only [EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
      ) hs.1 x]
  constructor
  · rintro ⟨hx, hheight⟩
    refine ⟨hx, ?_⟩
    simpa only [EpsilonNeck.coordinatePartialHomeomorph_symm_apply,
      mem_Ioo] using hheight
  · rintro ⟨hx, hheight⟩
    refine ⟨hx, ?_⟩
    simpa only [EpsilonNeck.coordinatePartialHomeomorph_symm_apply,
      mem_Ioo] using hheight


structure ClosedModelCapTubeAttachment
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X)
    (side : Bool) where
  overlap_model : OpenCylinderModel (cap.carrier ∩ tube.carrier)
  tube_tail : ∃ a ∈ Ioo (0 : ℝ) 1, tube.cylinder.tail side a ⊆ cap.carrier
  cap_tail : ∃ s ∈ Ioo 0 cap.epsilon⁻¹,
    cap.end_chart.cylinderTail cap.epsilon⁻¹ s ⊆ tube.carrier

noncomputable def ClosedModelCapTubeAttachment.ofCapTubeAttachment
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    {C : CapCertificate g} {T : EpsilonTubeCertificate g X} {side : Bool}
    (A : CapTubeAttachment C T side) :
    ClosedModelCapTubeAttachment
      (ClosedModelCapData.ofCapCertificate C) T side := by
  refine
    { overlap_model := A.overlap_model
      tube_tail := A.tube_tail
      cap_tail := ?_ }
  rcases A.cap_tail with ⟨s, hs, htail⟩
  have hs' : s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    have hL : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
    exact ⟨(neg_lt_zero.mpr hL).trans hs.1, hs.2⟩
  refine ⟨s, hs, ?_⟩
  have heq :
      (ClosedModelCapData.ofCapCertificate C).end_chart.cylinderTail
          (ClosedModelCapData.ofCapCertificate C).epsilon⁻¹ s =
        C.end_neck.region s C.epsilon⁻¹ := by
    simpa only [ClosedModelCapData.ofCapCertificate] using
      ClosedModelCapData.ofCapCertificate_end_chart_tail C hs'
  rw [heq]
  exact htail

end PoincareConjecture.M25.Topology3D
