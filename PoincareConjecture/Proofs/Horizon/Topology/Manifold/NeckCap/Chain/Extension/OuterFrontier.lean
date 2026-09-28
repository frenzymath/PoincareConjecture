import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Ends
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem mem_coordinate_slab_iff (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) {x : M} :
    x ∈ N.coordinate_map '' (univ ×ˢ Icc a b) ↔
      x ∈ N.carrier ∧ a ≤ (N.coordinate_inverse x).2 ∧
        (N.coordinate_inverse x).2 ≤ b := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hdom : z ∈ N.cylinderDomain :=
      ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
    exact ⟨N.coordinate_map_mem hdom,
      by simpa [N.coordinate_inverse_coordinate_map hdom] using hz.2⟩
  · rintro ⟨hx, hab⟩
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hab⟩,
      N.coordinate_map_coordinate_inverse hx⟩



theorem closure_positive_quarter_diff_carrier_subset (N N' : EpsilonNeck g)
    (hpos : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier)
    (hneg : N'.region (-N'.epsilon⁻¹) (-N'.epsilon⁻¹ / 2) ⊆ N.carrier)
    (hwithin : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        N'.region (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2)) :
    closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) \ N.carrier ⊆ N'.carrier := by
  let r := N.epsilon⁻¹
  let s := N'.epsilon⁻¹
  have hr : 0 < r := inv_pos.mpr N.epsilon_pos
  have hs : 0 < s := inv_pos.mpr N'.epsilon_pos
  let c : ℝ := -3 * s / 4
  have hc : -s < c := by dsimp [c]; linarith
  have hcs : c < s := by dsimp [c]; linarith
  have hchalf : c < -s / 2 := by dsimp [c]; linarith
  let K := N'.coordinate_map '' (univ ×ˢ Icc c c)
  have hKcompact : IsCompact K := N'.isCompact_coordinate_slab hc hcs
  have hKsub : K ⊆ N.carrier := by
    intro x hx
    obtain ⟨hx', hcl, hcu⟩ := (mem_coordinate_slab_iff N' hc hcs).mp hx
    apply hneg
    exact ⟨hx', by change -s < _; linarith, by change _ < -s / 2; linarith⟩
  have hKne : K.Nonempty := by
    exact ⟨N'.coordinate_map ((N'.coordinate_inverse N'.center).1, c),
      ((N'.coordinate_inverse N'.center).1, c), ⟨mem_univ _, le_rfl, le_rfl⟩, rfl⟩
  obtain ⟨z, hz, hmax⟩ := hKcompact.exists_isMaxOn hKne
    (N.coordinate_inverse_smooth.continuousOn.snd.mono hKsub)
  have hzr : (N.coordinate_inverse z).2 < r :=
    (N.coordinate_inverse_mem z (hKsub hz)).2.2
  obtain ⟨a, hmaxa, har⟩ := exists_between
    (show max (N.coordinate_inverse z).2 (r / 2) < r from
      max_lt hzr (by linarith))
  have hhalf : r / 2 < a := (le_max_right _ _).trans_lt hmaxa
  have hKa : ∀ x ∈ K, (N.coordinate_inverse x).2 < a := by
    intro x hx
    exact (hmax hx).trans_lt ((le_max_left _ _).trans_lt hmaxa)
  let T := N.region a r
  have hTsub : T ⊆ N'.carrier := by
    intro x hx
    exact hpos ⟨hx.1, hhalf.trans hx.2.1, hx.2.2⟩
  have hTconnected : IsConnected T :=
    N.isConnected_region (by change -r ≤ a; linarith) le_rfl har
  have hTne : ∀ x ∈ T, (N'.coordinate_inverse x).2 ≠ c := by
    intro x hx heq
    have hxK : x ∈ K :=
      (mem_coordinate_slab_iff N' hc hcs).mpr ⟨hTsub hx, heq.ge, heq.le⟩
    exact (hKa x hxK).not_gt hx.2.1
  have hTabove : ∀ x ∈ T, c < (N'.coordinate_inverse x).2 := by
    rcases hTconnected.2.mapsTo_Ioi_or_Iio
      (N'.coordinate_inverse_smooth.continuousOn.snd.mono hTsub) hTne with
      habove | hbelow
    · exact habove
    exfalso
    let S := N'.region c s
    have hSconnected : IsConnected S :=
      N'.isConnected_region hc.le le_rfl hcs
    have hSopen : IsOpen S := N'.isOpen_region c s
    let B := N.coordinate_map '' (univ ×ˢ Icc (-r / 2) a)
    have hBcompact : IsCompact B :=
      N.isCompact_coordinate_slab (by change -r < -r / 2; linarith) har
    have hBsub : B ⊆ N.carrier :=
      N.coordinate_slab_subset_carrier (by change -r < -r / 2; linarith) har
    have hinterB : N.carrier ∩ S ⊆ B := by
      intro x hx
      have hover := hwithin ⟨hx.1, hx.2.1⟩
      apply (mem_coordinate_slab_iff N
        (by change -r < -r / 2; linarith) har).mpr
      refine ⟨hx.1, hover.1.2.1.le, ?_⟩
      by_contra hxa
      have hxT : x ∈ T :=
        ⟨hx.1, lt_of_not_ge hxa, (N.coordinate_inverse_mem x hx.1).2.2⟩
      exact (hbelow hxT).not_gt hx.2.2.1
    have hmeet : (S ∩ (N.carrier ∩ S)).Nonempty := by
      obtain ⟨x, hx⟩ := (N'.isConnected_region hc.le
        (show -s / 2 ≤ N'.epsilon⁻¹ by change -s / 2 ≤ s; linarith)
        hchalf).1
      have hxS : x ∈ S := ⟨hx.1, hx.2.1, hx.2.2.trans (by linarith)⟩
      have hxN : x ∈ N.carrier :=
        hneg ⟨hx.1, hc.trans hx.2.1, hx.2.2⟩
      exact ⟨x, hxS, hxN, hxS⟩
    have hSsub : S ⊆ N.carrier ∩ S :=
      hSconnected.2.subset_of_closure_inter_subset (N.carrier_open.inter hSopen)
        hmeet (by
          intro x hx
          exact ⟨hBsub ((closure_minimal hinterB hBcompact.isClosed) hx.1), hx.2⟩)
    obtain ⟨x, hx⟩ := (N'.isConnected_region
      (show -N'.epsilon⁻¹ ≤ s / 2 by change -s ≤ s / 2; linarith)
      le_rfl (show s / 2 < N'.epsilon⁻¹ by change s / 2 < s; linarith)).1
    have hxS : x ∈ S := ⟨hx.1, (by dsimp [c]; linarith [hx.2.1]), hx.2.2⟩
    exact ((hwithin ⟨(hSsub hxS).1, hx.1⟩).2.2.2).not_gt hx.2.1
  let B' := N'.coordinate_map '' (univ ×ˢ Icc c (s / 2))
  have hB'compact : IsCompact B' :=
    N'.isCompact_coordinate_slab hc (by change s / 2 < s; linarith)
  have hB'sub : B' ⊆ N'.carrier :=
    N'.coordinate_slab_subset_carrier hc (by change s / 2 < s; linarith)
  have hTB' : T ⊆ B' := by
    intro x hx
    exact (mem_coordinate_slab_iff N' hc
      (by change s / 2 < s; linarith)).mpr
      ⟨hTsub hx, (hTabove x hx).le, (hwithin ⟨hx.1, hTsub hx⟩).2.2.2.le⟩
  have hclosureT : closure T ⊆ N'.carrier :=
    (closure_minimal hTB' hB'compact.isClosed).trans hB'sub
  let B := N.coordinate_map '' (univ ×ˢ Icc (r / 2) a)
  have hBcompact : IsCompact B :=
    N.isCompact_coordinate_slab (by change -r < r / 2; linarith) har
  have hBsub : B ⊆ N.carrier :=
    N.coordinate_slab_subset_carrier (by change -r < r / 2; linarith) har
  have hquarter : N.region (r / 2) r ⊆ B ∪ T := by
    intro x hx
    by_cases hxa : a < (N.coordinate_inverse x).2
    · exact Or.inr ⟨hx.1, hxa, hx.2.2⟩
    · exact Or.inl ((mem_coordinate_slab_iff N
        (by change -r < r / 2; linarith) har).mpr
        ⟨hx.1, hx.2.1.le, le_of_not_gt hxa⟩)
  intro x hx
  have hxc := closure_mono hquarter hx.1
  rw [closure_union, hBcompact.isClosed.closure_eq] at hxc
  exact hxc.elim (fun hxB => False.elim (hx.2 (hBsub hxB))) (hclosureT ·)

end PoincareConjecture.EpsilonNeck
