import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Diffeomorph.EssentialSphere.CapComponents
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions

open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture
open _root_.PoincareConjecture.CapCertificate

namespace M38Schoenflies

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_essential_overlap_slice_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g), C.epsilon ≤ ε₀ →
          ∀ {U : Set M}, IsOpen U → U ⊆ C.carrier →
            OpenCylinderModel U →
            (∃ a ∈ Ioo 0 C.epsilon⁻¹, C.end_neck.region a C.epsilon⁻¹ ⊆ U) →
            ∃ s ∈ Ioo 0 C.epsilon⁻¹, ∃ δ : ℝ,
              0 < δ ∧ 0 < s - δ ∧ s + δ < C.epsilon⁻¹ ∧
              C.end_neck.region (s - δ) C.epsilon⁻¹ ⊆ U ∧
              let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
              IsCompact K ∧ K ⊆ C.carrier ∧
                interior K = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) s ∧
                frontier K = range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, s)) ∧
                C.closed_core ⊆ interior K ∧
                U \ K = C.end_neck.region s C.epsilon⁻¹ ∧
                IsConnected (U ∩ interior K) ∧ IsConnected (U \ K) ∧
                (U ∩ interior K) ∪ (U \ K) = U \ frontier K ∧
                (∀ x ∈ U ∩ interior K,
                  connectedComponentIn (U \ frontier K) x = U ∩ interior K) ∧
                (∀ x ∈ U \ K, connectedComponentIn (U \ frontier K) x = U \ K) ∧
                ∀ L : Set M, IsCompact L → L ⊆ U →
                  ¬ U ∩ interior K ⊆ L ∧ ¬ U \ K ⊆ L := by
  obtain ⟨ε₁, hε₁, hsmall, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  obtain ⟨ε₂, hε₂, _, havoid⟩ := exists_positive_tail_disjoint_compact_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε U hU hUC T htail
  obtain ⟨a, ha, haU⟩ := htail
  let S := T.coordinate '' (univ ×ˢ Icc (1 / 2 : ℝ) (1 / 2))
  have hS : IsCompact S := T.isCompact_coordinate_slab (by norm_num) (by norm_num)
  have hSU : S ⊆ U := T.coordinate_slab_subset (by norm_num) (by norm_num)
  obtain ⟨b, hb, hbS⟩ := havoid C (hε.trans (min_le_right _ _)) hS (hSU.trans hUC)
  let c := max a b
  have hc : c ∈ Ioo 0 C.epsilon⁻¹ :=
    ⟨ha.1.trans_le (le_max_left _ _), max_lt ha.2 hb.2⟩
  let s := (c + C.epsilon⁻¹) / 2
  let δ := (C.epsilon⁻¹ - c) / 4
  have hs : s ∈ Ioo 0 C.epsilon⁻¹ := by dsimp [s]; constructor <;> linarith [hc.1, hc.2]
  have hδ : 0 < δ := by dsimp [δ]; linarith [hc.2]
  have hcs : c < s - δ := by dsimp [s, δ]; linarith [hc.2]
  have hlo : 0 < s - δ := hc.1.trans hcs
  have hhi : s + δ < C.epsilon⁻¹ := by dsimp [s, δ]; linarith [hc.2]
  have htailU : C.end_neck.region (s - δ) C.epsilon⁻¹ ⊆ U := by
    intro x hx
    exact haU ⟨hx.1, ((le_max_left _ _).trans_lt hcs).trans hx.2.1, hx.2.2⟩
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  obtain ⟨hK, hKC, hint, hfront, _, hcore⟩ := htrunc C
    (hε.trans (min_le_left _ _)) s ⟨(neg_lt_zero.mpr hR).trans hs.1, hs.2⟩
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
  let P := C.end_neck.region s C.epsilon⁻¹
  have hPU : P ⊆ U := fun x hx => htailU ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
  have hCdiff : C.carrier \ K = P := by
    ext x
    constructor
    · rintro ⟨hxC, hxK⟩
      have hxend := ((CapCertificate.carrier_eq_closed_core_union_end C) ▸ hxC).resolve_left
        (fun hx => hxK (Or.inl hx))
      have hz := (C.end_neck.coordinate_inverse_mem x hxend).2
      rw [C.end_neck_epsilon] at hz
      refine ⟨hxend, ?_, hz.2⟩
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
      · exact hxK (interior_subset (hint.symm ▸ Or.inr ⟨hxend, hz.1, hlt⟩))
      · apply hxK
        apply hK.isClosed.frontier_subset
        rw [hfront]
        refine ⟨(C.end_neck.coordinate_inverse x).1, ?_⟩
        rw [← heq]
        exact C.end_neck.coordinate_map_coordinate_inverse hxend
    · intro hx
      refine ⟨C.end_neck_subset hx.1, ?_⟩
      intro hxK
      by_cases hxi : x ∈ interior K
      · rcases hint ▸ hxi with hxcore | hxneg
        · exact disjoint_left.mp (CapCertificate.disjoint_closed_core_end C) hxcore hx.1
        · exact lt_asymm hxneg.2.2 hx.2.1
      · have hxf : x ∈ frontier K := hK.isClosed.frontier_eq.symm ▸ ⟨hxK, hxi⟩
        obtain ⟨q, hq⟩ := hfront.subset hxf
        have hdom : (q, s) ∈ C.end_neck.cylinderDomain := by
          rw [EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
          exact ⟨mem_univ _, (neg_lt_zero.mpr hR).trans hs.1, hs.2⟩
        have hh := hx.2.1
        rw [← hq, C.end_neck.coordinate_inverse_coordinate_map hdom] at hh
        exact lt_irrefl _ hh
  have hUdiff : U \ K = P := by
    apply Subset.antisymm
    · exact fun x hx => hCdiff.subset ⟨hUC hx.1, hx.2⟩
    · exact fun x hx => ⟨hPU hx, (hCdiff.superset hx).2⟩
  have hcollar : C.end_neck.region (s - δ) (s + δ) ⊆ U := by
    intro x hx
    exact htailU ⟨hx.1, hx.2.1, hx.2.2.trans hhi⟩
  obtain ⟨hcA, hcB, hcover, hcompA, hcompB⟩ := CapCertificate.truncated_sides_components C
    hU T.isConnected_carrier hK.isClosed hδ ((neg_lt_zero.mpr hR).trans hlo)
    hhi hcollar hint hfront
  have hPS : Disjoint P S := by
    apply disjoint_left.mpr
    intro x hx hxS
    exact disjoint_left.mp hbS hxS ⟨hx.1,
      ((le_max_right _ _).trans_lt hcs).trans (by linarith [hx.2.1]), hx.2.2⟩
  have hPconn : IsConnected P := by
    apply C.end_neck.isConnected_region
    · rw [C.end_neck_epsilon]; linarith [hs.1]
    · rw [C.end_neck_epsilon]
    · exact hs.2
  have hhalf :
      (∀ x ∈ P, (T.inverse x).2 < 1 / 2) ∨
        (∀ x ∈ P, 1 / 2 < (T.inverse x).2) := by
    have hcHeight : IsPreconnected ((fun x => (T.inverse x).2) '' P) :=
      hPconn.isPreconnected.image _ (T.inverse_smooth.continuousOn.snd.mono hPU)
    have hHeight : (fun x => (T.inverse x).2) '' P ⊆ Iio (1 / 2) ∪ Ioi (1 / 2) := by
      rintro t ⟨x, hx, rfl⟩
      have hne : (T.inverse x).2 ≠ 1 / 2 := by
        intro heq
        exact disjoint_left.mp hPS hx
          ⟨T.inverse x, ⟨mem_univ _, heq.ge, heq.le⟩, T.right_inverse (hPU hx)⟩
      exact lt_or_gt_of_ne hne
    rcases hcHeight.subset_or_subset isOpen_Iio isOpen_Ioi
      (disjoint_left.mpr fun _ hl hr => lt_asymm hl hr) hHeight with hh | hh
    · exact Or.inl fun x hx => hh (mem_image_of_mem _ hx)
    · exact Or.inr fun x hx => hh (mem_image_of_mem _ hx)
  refine ⟨s, hs, δ, hδ, hlo, hhi, htailU, hK, hKC, hint, hfront, hcore,
    hUdiff, hcA, hcB, hcover, hcompA, hcompB, ?_⟩
  intro L hL hLU
  constructor
  · intro hAL
    have hfU : frontier K ⊆ U := by
      rw [hfront]
      rintro x ⟨q, rfl⟩
      have hdom : (q, s) ∈ C.end_neck.cylinderDomain := by
        rw [EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
        exact ⟨mem_univ _, (neg_lt_zero.mpr hR).trans hs.1, hs.2⟩
      apply hcollar
      refine ⟨C.end_neck.coordinate_map_mem hdom, ?_⟩
      rw [C.end_neck.coordinate_inverse_coordinate_map hdom]
      constructor <;> dsimp <;> linarith
    obtain ⟨r, hr, hn, hp, _, _⟩ := T.exists_tails_disjoint_of_isCompact
      (hL.union (hK.of_isClosed_subset isClosed_frontier
        hK.isClosed.frontier_subset)) (union_subset hLU hfU)
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, by linarith [hr.2]⟩
    have hrc : 1 - r ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hr.1, hr.2]
    have hpoint (x : M) (hxU : x ∈ U) (hxP : x ∉ P)
        (hxavoid : x ∉ L ∪ frontier K) : False := by
      have hxK : x ∈ K := by
        by_contra h
        exact hxP (hUdiff.subset ⟨hxU, h⟩)
      have hxi : x ∈ interior K := by
        by_contra h
        exact hxavoid (Or.inr (hK.isClosed.frontier_eq.symm ▸ ⟨hxK, h⟩))
      exact hxavoid (Or.inl (hAL ⟨hxU, hxi⟩))
    rcases hhalf with hh | hh
    · obtain ⟨x, hx⟩ := (T.isConnected_tail true hrc).nonempty
      have hxt := (T.mem_tail_iff true hrc).mp hx
      exact hpoint x hxt.1 (fun hxP => by have h := hh x hxP; dsimp at hxt; linarith [hr.2])
        (fun hxL => disjoint_left.mp hp hx hxL)
    · obtain ⟨x, hx⟩ := (T.isConnected_tail false hr01).nonempty
      have hxt := (T.mem_tail_iff false hr01).mp hx
      exact hpoint x hxt.1 (fun hxP => by have h := hh x hxP; dsimp at hxt; linarith [hr.2])
        (fun hxL => disjoint_left.mp hn hx hxL)
  · intro hBL
    have hEq : C.carrier = K ∪ L := by
      apply Subset.antisymm
      · intro x hxC
        by_cases hxK : x ∈ K
        · exact Or.inl hxK
        · exact Or.inr (hBL (hUdiff.superset (hCdiff.subset ⟨hxC, hxK⟩)))
      · exact union_subset hKC (hLU.trans hUC)
    exact C.not_isCompact_carrier (hEq ▸ hK.union hL)

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.CapTubeAttachment

theorem exists_essential_slice_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {X : Set M},
        ∀ {C : CapCertificate g} {T : EpsilonTubeCertificate g X} {side : Bool},
          CapTubeAttachment C T side → C.epsilon ≤ ε₀ →
          let U := C.carrier ∩ T.carrier
          ∃ s ∈ Ioo 0 C.epsilon⁻¹, ∃ δ : ℝ,
            0 < δ ∧ 0 < s - δ ∧ s + δ < C.epsilon⁻¹ ∧
            C.end_neck.region (s - δ) C.epsilon⁻¹ ⊆ U ∧
            let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
            IsCompact K ∧ K ⊆ C.carrier ∧
              interior K = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) s ∧
              frontier K = range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, s)) ∧
              C.closed_core ⊆ interior K ∧
              U \ K = C.end_neck.region s C.epsilon⁻¹ ∧
              IsConnected (U ∩ interior K) ∧ IsConnected (U \ K) ∧
              (U ∩ interior K) ∪ (U \ K) = U \ frontier K ∧
              (∀ x ∈ U ∩ interior K,
                connectedComponentIn (U \ frontier K) x = U ∩ interior K) ∧
              (∀ x ∈ U \ K, connectedComponentIn (U \ frontier K) x = U \ K) ∧
              ∀ L : Set M, IsCompact L → L ⊆ U →
                ¬ U ∩ interior K ⊆ L ∧ ¬ U \ K ⊆ L := by
  obtain ⟨ε₀, hε₀, hsmall, hslice⟩ :=
    CapCertificate.exists_essential_overlap_slice_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g X C T side A hC
  apply hslice C hC (C.carrier_open.inter T.carrier_open) inter_subset_left A.overlap_model
  obtain ⟨a, ha, htail⟩ := A.cap_tail
  exact ⟨a, ha, fun x hx => ⟨C.end_neck_subset hx.1, htail hx⟩⟩

end PoincareConjecture.CapTubeAttachment

end M38Schoenflies
