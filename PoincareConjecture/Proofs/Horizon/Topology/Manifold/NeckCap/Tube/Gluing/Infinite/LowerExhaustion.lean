import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InteriorThickness
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Chart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Cylinder













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem eighth_width_le_edist_of_not_mem_upper_region (N : EpsilonNeck g) {p x : M}
    (hp : p ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))
    (hx : x ∉ N.region (-(3 / 4 : ℝ) * N.epsilon⁻¹) N.epsilon⁻¹) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8)) ≤
      g.edist p x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi := inv_pos.mpr N.epsilon_pos
  let s : ℝ := (5 / 8 : ℝ) * N.epsilon⁻¹
  have hs : s ∈ Ioo 0 N.epsilon⁻¹ := by dsimp [s]; constructor <;> linarith
  by_contra h
  have hdist : Manifold.riemannianEDist (𝓡 3) p x <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8)) :=
    lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdist (show (0 : ℝ) < 1 by norm_num)
  have hstart : γ 0 ∈ N.region (-s) s := by
    rw [hγ0]
    refine ⟨hp.1, ?_, ?_⟩ <;> dsimp [s] <;> linarith [hp.2.1, hp.2.2]
  have hout : γ 1 ∉ N.coordinate_map '' (univ ×ˢ Icc (-s) s) := by
    rw [hγ1]
    intro hmem
    have h := (N.mem_coordinate_slab_iff (neg_lt_neg hs.2) hs.2).mp hmem
    apply hx
    refine ⟨h.1, ?_, ?_⟩ <;> dsimp [s] at h <;> linarith [h.2.1, h.2.2]
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (show (0 : ℝ) ≤ 1 by norm_num) (neg_lt_neg hs.2) hs.2
    hγ.continuous.continuousOn hstart hout
  have hvalue : N.epsilon⁻¹ / 8 ≤ |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| := by
    rw [hγ0]
    rcases hboundary with hneg | hpos
    · rw [hneg]
      have h := le_abs_self (-s - (N.coordinate_inverse p).2)
      have h' := neg_le_abs (-s - (N.coordinate_inverse p).2)
      dsimp [s] at h h'
      linarith [hp.2.1]
    · rw [hpos]
      have h := le_abs_self (s - (N.coordinate_inverse p).2)
      dsimp [s] at h
      linarith [hp.2.2]
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  have hax := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hvalue hfactor)).trans
    (N.axial_displacement_le_pathELength ht.1.le hγ hcarrier)
  exact (not_lt_of_ge (hax.trans (Manifold.pathELength_mono le_rfl ht.2))) hlength




theorem lower_half_images_exhaust_of_neck_tails
    (N : ℕ → EpsilonNeck g) {ε : ℝ} (hε : ∀ n, (N n).epsilon = ε)
    (U : ℕ → Opens M) (hU : Monotone U)
    (hconnected : IsConnected (⋃ n, (U n : Set M)))
    (F : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (U n) ∞)
    (T : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (N n).carrierOpen ∞)
    (htail : ∀ n (p : RoundCylinderSpace), 0 < p.2 → (F n p : M) = T n p)
    (hside : ∀ n (p : RoundCylinderSpace),
      -(3 / 4 : ℝ) * ε⁻¹ < ((N n).coordinate_inverse (T n p)).2 ↔ 0 < p.2)
    (hwithin : ∀ n, (N n).carrier ∩ (N (n + 1)).carrier ⊆
      (N n).region (-ε⁻¹ / 2) ε⁻¹ ∩ (N (n + 1)).region (-ε⁻¹) (ε⁻¹ / 2))
    (hretain : ∀ n (p : RoundCylinderSpace), p.2 ≤ 0 →
      ∃ q : RoundCylinderSpace, q.2 < 0 ∧ (F (n + 1) q : M) = F n p) :
    ∀ x ∈ ⋃ n, (U n : Set M),
      ∃ n, ∃ p : RoundCylinderSpace, p.2 < 0 ∧ (F n p : M) = x := by
  let L (n : ℕ) : Set M := (fun p : RoundCylinderSpace => (F n p : M)) '' {p | p.2 ≤ 0}
  let V (n : ℕ) : Set M := (fun p : RoundCylinderSpace => (F n p : M)) '' {p | p.2 < 0}
  let W : Set M := ⋃ n, V n
  have hVL (n : ℕ) : V n ⊆ L n :=
    image_mono fun p (hp : p.2 < 0) => (show p.2 ≤ 0 from hp.le)
  have hLV (n : ℕ) : L n ⊆ V (n + 1) := by
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨q, hq, heq⟩ := hretain n p hp
    exact ⟨q, hq, heq⟩
  have hLmono : Monotone L := monotone_nat_of_le_succ fun n => (hLV n).trans (hVL (n + 1))
  have hLW (n : ℕ) : L n ⊆ W := (hLV n).trans (subset_iUnion V (n + 1))
  have hWopen : IsOpen W := isOpen_iUnion fun n =>
    ((U n).isOpenEmbedding'.isOpenMap.comp (F n).toHomeomorph.isOpenMap) _
      (isOpen_lt continuous_snd continuous_const)
  have hWsub : W ⊆ ⋃ n, (U n : Set M) := by
    intro x hx
    obtain ⟨n, p, _, rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, (F n p).property⟩
  have hWnonempty : W.Nonempty := by
    let q := ((N 0).coordinate_inverse (N 0).center).1
    exact ⟨F 0 (q, -1), mem_iUnion.mpr ⟨0, (q, -1), by norm_num, rfl⟩⟩
  have hLoutside (n : ℕ) {y : M} (hy : y ∈ L n) :
      y ∉ (N n).region (-(3 / 4 : ℝ) * ε⁻¹) ε⁻¹ := by
    rintro hytail
    obtain ⟨p, hp, rfl⟩ := hy
    let q := (T n).symm ⟨F n p, hytail.1⟩
    have hTq : (T n q : M) = F n p := congrArg Subtype.val ((T n).apply_symm_apply _)
    have hq : 0 < q.2 := (hside n q).1 (by rw [hTq]; exact hytail.2.1)
    have hFp : F n q = F n p := Subtype.ext ((htail n q hq).trans hTq)
    have heq := (F n).injective hFp
    exact (not_lt_of_ge hp) (heq ▸ hq)
  have hclosed : closure W ∩ (⋃ n, (U n : Set M)) ⊆ W := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    intro x hx
    by_contra hout
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx.2
    have hxN (m : ℕ) (hm : k ≤ m) : x ∈ (N m).carrier := by
      let p := (F m).symm ⟨x, hU hm hxk⟩
      have hp : (F m p : M) = x := congrArg Subtype.val ((F m).apply_symm_apply _)
      have hpos : 0 < p.2 := by
        by_contra h
        exact hout (hLW m ⟨p, le_of_not_gt h, hp⟩)
      rw [← hp, htail m p hpos]
      exact (T m p).property
    have hxmid (m : ℕ) (hm : k + 1 ≤ m) :
        x ∈ (N m).region (-ε⁻¹ / 2) (ε⁻¹ / 2) := by
      have hnext := hwithin m ⟨hxN m (by omega), hxN (m + 1) (by omega)⟩
      have heq : m - 1 + 1 = m := by omega
      have hprev := hwithin (m - 1) ⟨hxN (m - 1) (by omega),
        heq.symm ▸ hxN m (by omega)⟩
      rw [heq] at hprev
      exact ⟨hxN m (by omega), hnext.1.2.1, hprev.2.2.2⟩
    obtain ⟨ρ, hρ, hbound⟩ := exists_scale_lower_bound_of_meets_compact
      (N 0).connection ε (isCompact_singleton (x := x))
    have hepos : 0 < ε := hε 0 ▸ (N 0).epsilon_pos
    have hroot : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.mpr (by
      have hsmall := (N 0).epsilon_lt_half
      rw [hε 0] at hsmall
      linarith)
    let R := ENNReal.ofReal (ρ * Real.sqrt (1 - ε) * (ε⁻¹ / 8))
    have hR : 0 < R := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨y, hyball, hyW⟩ := mem_closure_iff_nhds.mp hx.1
      (Metric.eball x R) (Metric.eball_mem_nhds x hR)
    obtain ⟨n, hyn⟩ := mem_iUnion.mp hyW
    let m := max n (k + 1)
    have hym : y ∈ L m := hLmono (le_max_left _ _) (hVL n hyn)
    have hxm := hxmid m (le_max_right _ _)
    have hscale : ρ ≤ (N m).scale := hbound (N m) (hε m)
      ⟨x, hxm.1, mem_singleton x⟩
    have hlower := (N m).eighth_width_le_edist_of_not_mem_upper_region
      (by simpa only [hε m] using hxm)
      (by simpa only [hε m] using hLoutside m hym)
    rw [hε m] at hlower
    have hle : R ≤ g.edist x y := by
      apply (ENNReal.ofReal_le_ofReal ?_).trans hlower
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hroot.le)
        (by positivity)
    change g.edist y x < R at hyball
    have hsym : g.edist x y = g.edist y x := Manifold.riemannianEDist_comm
    rw [hsym] at hle
    exact (not_lt_of_ge hle) hyball
  have hcover : (⋃ n, (U n : Set M)) ⊆ W ∪ (closure W)ᶜ := by
    intro x hx
    by_cases h : x ∈ closure W
    · exact Or.inl (hclosed ⟨h, hx⟩)
    · exact Or.inr h
  have hdisjoint : Disjoint W (closure W)ᶜ := disjoint_compl_right.mono_left subset_closure
  have hsubset := hconnected.isPreconnected.subset_left_of_subset_union
    hWopen isClosed_closure.isOpen_compl hdisjoint hcover
    (hWnonempty.mono fun x hx => ⟨hWsub hx, hx⟩)
  intro x hx
  exact mem_iUnion.mp (hsubset hx)




theorem exists_cylinder_of_neck_tails
    (N : ℕ → EpsilonNeck g) {ε : ℝ} (hε : ∀ n, (N n).epsilon = ε)
    (U : ℕ → Opens M) (hU : Monotone U)
    (hconnected : IsConnected (⋃ n, (U n : Set M)))
    (F : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (U n) ∞)
    (T : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (N n).carrierOpen ∞)
    (E : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (htail : ∀ n (p : RoundCylinderSpace), 0 < p.2 → (F n p : M) = T n p)
    (hside : ∀ n (p : RoundCylinderSpace),
      -(3 / 4 : ℝ) * ε⁻¹ < ((N n).coordinate_inverse (T n p)).2 ↔ 0 < p.2)
    (hwithin : ∀ n, (N n).carrier ∩ (N (n + 1)).carrier ⊆
      (N n).region (-ε⁻¹ / 2) ε⁻¹ ∩ (N (n + 1)).region (-ε⁻¹) (ε⁻¹ / 2))
    (hretain : ∀ n (p : RoundCylinderSpace), p.2 ≤ 0 →
      (F (n + 1) ((E n).symm p) : M) = F n p)
    (hE : ∀ n (p : RoundCylinderSpace), p.2 ≤ 0 → ((E n).symm p).2 < 0) :
    ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(⨆ n, U n) ∞,
      ∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = F 0 p := by
  have hcover := lower_half_images_exhaust_of_neck_tails N hε U hU hconnected F T
    htail hside hwithin (fun n p hp => ⟨(E n).symm p, hE n p hp, hretain n p hp⟩)
  obtain ⟨D, _, _, _, hfirst⟩ := CylinderGluing.exists_cylinder_of_relative_extensions U F E
    hretain hE (by
      intro x hx
      have hx' : x ∈ ⋃ n, (U n : Set M) := mem_iUnion.mpr (Opens.mem_iSup.mp hx)
      obtain ⟨n, p, hp, heq⟩ := hcover x hx'
      exact ⟨n, p, hp.le, heq⟩)
  exact ⟨D, hfirst⟩

end PoincareConjecture.EpsilonNeck
