import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Truncation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem mem_closure_region_iff (N : EpsilonNeck g) {a b : ℝ}
    (hab : a < b) {x : M} (hx : x ∈ N.carrier) :
    x ∈ closure (N.region a b) ↔
      a ≤ (N.coordinate_inverse x).2 ∧ (N.coordinate_inverse x).2 ≤ b := by
  have himage : N.coordinatePartialHomeomorph.symm.IsImage
      (N.region a b) ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) := by
    intro y hy
    change (N.coordinate_inverse y).1 ∈ univ ∧
      (N.coordinate_inverse y).2 ∈ Ioo a b ↔
        y ∈ N.carrier ∧ a < (N.coordinate_inverse y).2 ∧
          (N.coordinate_inverse y).2 < b
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ N.carrier from hy]
  have h := himage.closure.apply_mem_iff hx
  change N.coordinate_inverse x ∈ closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) ↔
    x ∈ closure (N.region a b) at h
  simpa only [closure_prod_eq, closure_univ, closure_Ioo hab.ne,
    mem_prod, mem_univ, true_and, mem_Icc] using h.symm




theorem exists_finite_chain_enclosing_region_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T →
          ∀ b : ℤ, T.shape = .finite 0 b →
          ∀ {S : Set M}, IsCompact S → S ⊆ C.carrier ∪ (T.unionOpen : Set M) →
            ∃ U : Set M, IsOpen U ∧ IsCompact (closure U) ∧
              closure U ⊆ C.carrier ∪ (T.unionOpen : Set M) ∧
              S ⊆ U ∧ IsConnected (frontier U) := by
  obtain ⟨ε₀, hε₀, hsmall, htruncate⟩ := exists_finite_chain_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT b hshape S hS hSA
  classical
  let R := C.epsilon⁻¹
  have hR : 0 < R := inv_pos.mpr C.epsilon_pos
  have hbnonneg : 0 ≤ b := by
    have h := hT.zero_active
    simpa only [hshape, ChainShape.active, mem_Icc, le_refl, true_and] using h
  have hb : b ∈ T.shape.active := by
    simp only [hshape, ChainShape.active, mem_Icc]
    exact ⟨hbnonneg, le_rfl⟩
  let N := T.neck b
  have heN : N.epsilon = C.epsilon := T.epsilon_eq b hb
  let A := C.carrier ∪ (T.unionOpen : Set M)
  let K (t : Ioo (R / 2) R) := A \ N.region t R
  let U (t : Ioo (R / 2) R) := interior (K t)
  have hcut (t : Ioo (R / 2) R) := htruncate C hε H T hT b hshape t t.property
  have hNA : N.carrier ⊆ A := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  have hlower (t : Ioo (R / 2) R) : N.region (-R) t ⊆ U t := by
    apply (N.isOpen_region _ _).subset_interior_iff.mpr
    intro x hx
    exact ⟨hNA hx.1, fun hp => (not_lt_of_ge hx.2.2.le) hp.2.1⟩
  have hs : (3 / 4 : ℝ) * R ∈ Ioo (R / 2) R := by constructor <;> linarith
  let s : Ioo (R / 2) R := ⟨_, hs⟩
  let : Nonempty (Ioo (R / 2) R) := ⟨s⟩
  have hcover : A ⊆ ⋃ t, U t := by
    intro x hx
    by_cases hxs : x ∈ U s
    · exact mem_iUnion.mpr ⟨s, hxs⟩
    have hxN : x ∈ N.carrier := by
      by_cases hp : x ∈ N.region s R
      · exact hp.1
      have hxfront : x ∈ frontier (K s) :=
        ⟨subset_closure ⟨hx, hp⟩, hxs⟩
      rw [(hcut s).2.2.2.1] at hxfront
      obtain ⟨q, rfl⟩ := hxfront
      apply N.coordinate_map_mem
      exact ⟨mem_univ _, by rw [heN]; change -R < s.val; linarith [s.property.1],
        by rw [heN]; exact s.property.2⟩
    have hxheight := (N.coordinate_inverse_mem x hxN).2
    rw [heN] at hxheight
    obtain ⟨t, htlo, hthi⟩ := exists_between
      (max_lt (show R / 2 < R by linarith) hxheight.2)
    let t' : Ioo (R / 2) R := ⟨t, (le_max_left _ _).trans_lt htlo, hthi⟩
    refine mem_iUnion.mpr ⟨t', hlower t' ?_⟩
    exact ⟨hxN, hxheight.1, (le_max_right _ _).trans_lt htlo⟩
  have hmono {s t : Ioo (R / 2) R} (hst : s.val ≤ t.val) : U s ⊆ U t := by
    apply interior_mono
    intro x hx
    refine ⟨hx.1, fun hp => hx.2 ?_⟩
    exact ⟨hp.1, hst.trans_lt hp.2.1, hp.2.2⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro s t
    refine ⟨⟨max s.val t.val,
      s.property.1.trans_le (le_max_left _ _), max_lt s.property.2 t.property.2⟩,
      hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  obtain ⟨t, hSt⟩ := hS.elim_directed_cover U (fun _ => isOpen_interior)
    (hSA.trans hcover) hdir
  have hcompact : IsCompact (K t) := (hcut t).1
  have hfront : frontier (K t) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) := (hcut t).2.2.2.1
  have htvalid : -N.epsilon⁻¹ < t.val ∧ t.val < N.epsilon⁻¹ := by
    rw [heN]
    exact ⟨by change -R < t.val; linarith [t.property.1], t.property.2⟩
  have hregular : closure (U t) = K t := by
    apply Subset.antisymm
    · exact closure_minimal interior_subset hcompact.isClosed
    · intro x hx
      by_cases hxi : x ∈ U t
      · exact subset_closure hxi
      have hxf : x ∈ frontier (K t) := ⟨subset_closure hx, hxi⟩
      rw [hfront] at hxf
      obtain ⟨q, rfl⟩ := hxf
      have hdom : (q, t.val) ∈ (univ : Set UnitTwoSphere) ×ˢ
          Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, htvalid⟩
      apply closure_mono (hlower t)
      rw [mem_closure_region_iff N (show -R < t.val by linarith [t.property.1])
        (N.coordinate_map_mem hdom), N.coordinate_inverse_coordinate_map hdom]
      exact ⟨by linarith [t.property.1], le_rfl⟩
  have hfrontU : frontier (U t) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) := by
    change frontier (interior (K t)) = _
    rw [frontier, interior_interior, show closure (interior (K t)) = K t from hregular]
    simpa only [frontier, hcompact.isClosed.closure_eq] using hfront
  refine ⟨U t, isOpen_interior, hregular ▸ hcompact,
    hregular ▸ (hcut t).2.1, hSt, ?_⟩
  rw [hfrontU]
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  rw [← image_univ]
  apply isConnected_univ.image
  apply N.coordinate_map_smooth.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn
  intro q _
  exact ⟨mem_univ _, htvalid⟩

end PoincareConjecture.CapCertificate
