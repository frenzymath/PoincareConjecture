import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Core.TruncatedDomain







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



theorem exists_positive_tail_disjoint_compact_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
          ∀ {K : Set M}, IsCompact K → K ⊆ C.carrier →
            ∃ s ∈ Ioo 0 C.epsilon⁻¹, Disjoint K (C.end_neck.region s C.epsilon⁻¹) := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε K hK hKC
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  let U (s : Ioo 0 C.epsilon⁻¹) :=
    C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) s
  have hopen (s : Ioo 0 C.epsilon⁻¹) : IsOpen (U s) := by
    obtain ⟨-, -, heq, -⟩ := htrunc C hε s
      ⟨(neg_lt_zero.mpr hR).trans s.property.1, s.property.2⟩
    rw [show U s = interior
      (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)) from heq.symm]
    exact isOpen_interior
  have hcover : C.carrier ⊆ ⋃ s, U s := by
    intro x hx
    rcases (CapCertificate.carrier_eq_closed_core_union_end C) ▸ hx with hc | he
    · refine mem_iUnion.mpr ⟨⟨C.epsilon⁻¹ / 2, by constructor <;> linarith⟩, Or.inl hc⟩
    · have hh := (C.end_neck.coordinate_inverse_mem x he).2
      rw [C.end_neck_epsilon] at hh
      obtain ⟨s, hs, hsR⟩ := exists_between (max_lt hR hh.2)
      exact mem_iUnion.mpr ⟨⟨s, (le_max_left _ _).trans_lt hs, hsR⟩,
        Or.inr ⟨he, hh.1, (le_max_right _ _).trans_lt hs⟩⟩
  have hmono {s t : Ioo 0 C.epsilon⁻¹} (hst : s.val ≤ t.val) : U s ⊆ U t := by
    rintro x (hc | he)
    · exact Or.inl hc
    · exact Or.inr ⟨he.1, he.2.1, he.2.2.trans_le hst⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro s t
    exact ⟨⟨max s.val t.val, s.property.1.trans_le (le_max_left _ _),
      max_lt s.property.2 t.property.2⟩,
      hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  let : Nonempty (Ioo 0 C.epsilon⁻¹) :=
    ⟨⟨C.epsilon⁻¹ / 2, by constructor <;> linarith⟩⟩
  obtain ⟨s, hKs⟩ := hK.elim_directed_cover U hopen (hKC.trans hcover) hdir
  refine ⟨s, s.property, disjoint_left.mpr ?_⟩
  intro x hxK hxpos
  rcases hKs hxK with hc | hneg
  · exact disjoint_left.mp (CapCertificate.disjoint_closed_core_end C) hc hxpos.1
  · exact (not_lt_of_ge hneg.2.2.le) hxpos.2.1



theorem exists_second_cap_tail_of_compact_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), D.epsilon ≤ ε₀ →
          ∀ {U : Set M}, IsOpen U → C.end_neck.carrier ⊆ U →
            Disjoint C.closed_core D.carrier → IsCompact (C.carrier ∪ U ∪ D.carrier) →
            ∃ s ∈ Ioo 0 D.epsilon⁻¹, D.end_neck.region s D.epsilon⁻¹ ⊆ U := by
  obtain ⟨ε₀, hε₀, hsmall, htail⟩ := exists_positive_tail_disjoint_compact_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε U hU hend hdis hcompact
  let K := (C.carrier ∪ U ∪ D.carrier) \ (C.carrier ∪ U)
  have hK : IsCompact K := hcompact.diff (C.carrier_open.union hU)
  have hKD : K ⊆ D.carrier := fun x hx => hx.1.resolve_left hx.2
  obtain ⟨s, hs, havoid⟩ := htail D hε hK hKD
  refine ⟨s, hs, ?_⟩
  intro x hx
  have hxD := D.end_neck_subset hx.1
  have hxA : x ∈ C.carrier ∪ U := by
    by_contra hnot
    exact disjoint_left.mp havoid ⟨Or.inr hxD, hnot⟩ hx
  rcases hxA with hxC | hxU
  · rcases (CapCertificate.carrier_eq_closed_core_union_end C) ▸ hxC with hc | he
    · exact (disjoint_left.mp hdis hc hxD).elim
    · exact hend he
  · exact hxU

end PoincareConjecture.CapCertificate

end M38Schoenflies
