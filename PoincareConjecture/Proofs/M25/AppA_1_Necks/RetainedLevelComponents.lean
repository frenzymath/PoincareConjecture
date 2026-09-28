import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight












set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}





theorem exists_opposite_retained_components
    (N : EpsilonNeck g) (hsep : N.IsSeparating)
    {t : ℝ} (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ a b : M,
      a ∈ N.region (-N.epsilon⁻¹) t ∧
      b ∈ N.region t N.epsilon⁻¹ ∧
      let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
      let A := connectedComponentIn Sᶜ a
      let B := connectedComponentIn Sᶜ b
      N.region (-N.epsilon⁻¹) t ⊆ A ∧
      N.region t N.epsilon⁻¹ ⊆ B ∧
      A ≠ B ∧
      frontier A = S ∧ frontier B = S ∧
      A ∪ S ∪ B = connectedComponent N.center := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  obtain ⟨a₀, b₀, ha₀, hb₀, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components hsep
  obtain ⟨H, hH, hinside, hnegative, hpositive, _, _⟩ :=
    N.exists_saturatedAxialHeight hsep a₀ b₀ ha₀ hb₀
  have houtside : ∀ x ∈ connectedComponent N.center \ N.carrier,
      H x = -N.epsilon⁻¹ ∨ H x = N.epsilon⁻¹ := by
    intro x hx
    rw [← hcover] at hx
    rcases hx.1 with (hn | hs) | hp
    · exact Or.inl (hnegative x ⟨hn, hx.2⟩)
    · exact False.elim (hx.2 (N.central_sphere_subset hs))
    · exact Or.inr (hpositive x ⟨hp, hx.2⟩)
  let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
  have hmemS {x : M} : x ∈ S ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = t := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨N.coordinate_map_mem ⟨mem_univ _, ht⟩,
        congrArg Prod.snd (N.coordinate_inverse_map _ ht)⟩
    · rintro ⟨hx, he⟩
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      rw [← he]
      exact N.coordinate_map_inverse hx
  have hlevel {x : M} (hx : x ∈ connectedComponent N.center) (he : H x = t) : x ∈ S := by
    by_cases hxc : x ∈ N.carrier
    · exact hmemS.mpr ⟨hxc, (hinside x hxc).symm.trans he⟩
    · rcases houtside x ⟨hx, hxc⟩ with hn | hp
      · exact False.elim (ne_of_lt ht.1 (hn.symm.trans he))
      · exact False.elim (ne_of_gt ht.2 (hp.symm.trans he))
  let r := min (t + N.epsilon⁻¹) (N.epsilon⁻¹ - t) / 2
  have hmin : 0 < min (t + N.epsilon⁻¹) (N.epsilon⁻¹ - t) :=
    lt_min (by linarith [ht.1]) (by linarith [ht.2])
  have hr : 0 < r := half_pos hmin
  have hlo : -N.epsilon⁻¹ < t - r := by
    have hm := min_le_left (t + N.epsilon⁻¹) (N.epsilon⁻¹ - t)
    dsimp only [r]
    linarith
  have hhi : t + r < N.epsilon⁻¹ := by
    have hm := min_le_right (t + N.epsilon⁻¹) (N.epsilon⁻¹ - t)
    dsimp only [r]
    linarith
  have hshift (s : Ioo (-r) r) : t + (s : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor <;> linarith [s.property.1, s.property.2]
  let V := N.region (t - r) (t + r)
  let e : (UnitTwoSphere × Ioo (-r) r) ≃ₜ V :=
    { toFun := fun z => ⟨N.coordinate_map (z.1, t + (z.2 : ℝ)), by
        refine ⟨N.coordinate_map_mem ⟨mem_univ _, hshift z.2⟩, ?_, ?_⟩
        · rw [N.coordinate_inverse_map _ (hshift z.2)]
          dsimp only
          linarith [z.2.property.1]
        · rw [N.coordinate_inverse_map _ (hshift z.2)]
          dsimp only
          linarith [z.2.property.2]⟩
      invFun := fun x => ((N.coordinate_inverse x).1,
        ⟨(N.coordinate_inverse x).2 - t, by
          constructor <;> linarith [x.property.2.1, x.property.2.2]⟩)
      left_inv := by
        intro z
        apply Prod.ext
        · change (N.coordinate_inverse (N.coordinate_map (z.1, t + (z.2 : ℝ)))).1 = z.1
          exact congrArg Prod.fst
            (N.coordinate_inverse_map (z.1, t + (z.2 : ℝ)) (hshift z.2))
        · apply Subtype.ext
          change (N.coordinate_inverse (N.coordinate_map (z.1, t + (z.2 : ℝ)))).2 - t = _
          rw [N.coordinate_inverse_map _ (hshift z.2)]
          dsimp only
          ring
      right_inv := by
        intro x
        apply Subtype.ext
        change N.coordinate_map ((N.coordinate_inverse x).1,
          t + ((N.coordinate_inverse x).2 - t)) = x
        rw [show t + ((N.coordinate_inverse x).2 - t) = (N.coordinate_inverse x).2 by ring]
        exact N.coordinate_map_inverse x.property.1
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply N.coordinate_map_smooth.continuousOn.comp_continuous
        · exact continuous_fst.prodMk (continuous_const.add
            (continuous_subtype_val.comp continuous_snd))
        · intro z
          exact ⟨mem_univ _, hshift z.2⟩
      continuous_invFun := by
        have hc : Continuous (fun x : V => N.coordinate_inverse x) :=
          N.coordinate_inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
            (fun x => x.property.1)
        exact hc.fst.prodMk ((hc.snd.sub continuous_const).subtype_mk _) }
  have hcentral : range (fun q : UnitTwoSphere =>
      (e (q, ⟨0, neg_lt_zero.mpr hr, hr⟩) : M)) = S := by
    change range (fun q : UnitTwoSphere => N.coordinate_map (q, t + 0)) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
    simp only [add_zero]
  let Cminus := (fun z => (e z : M)) '' {z | (z.2 : ℝ) < 0}
  let Cplus := (fun z => (e z : M)) '' {z | 0 < (z.2 : ℝ)}
  have hminus : IsConnected Cminus := Poincare.Topology.isConnected_collar_negative hr e
  have hplus : IsConnected Cplus := Poincare.Topology.isConnected_collar_positive hr e
  have hminusRegion : Cminus ⊆ N.region (-N.epsilon⁻¹) t := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨(e z).property.1, (N.coordinate_inverse_mem _ (e z).property.1).2.1, ?_⟩
    change (N.coordinate_inverse (N.coordinate_map (z.1, t + (z.2 : ℝ)))).2 < t
    rw [N.coordinate_inverse_map _ (hshift z.2)]
    dsimp only
    change (z.2 : ℝ) < 0 at hz
    linarith
  have hplusRegion : Cplus ⊆ N.region t N.epsilon⁻¹ := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨(e z).property.1, ?_, (N.coordinate_inverse_mem _ (e z).property.1).2.2⟩
    change t < (N.coordinate_inverse (N.coordinate_map (z.1, t + (z.2 : ℝ)))).2
    rw [N.coordinate_inverse_map _ (hshift z.2)]
    dsimp only
    change 0 < (z.2 : ℝ) at hz
    linarith
  have hregionConnected (a b : ℝ) (hab : a < b)
      (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) : IsConnected (N.region a b) := by
    have hdom : univ ×ˢ Ioo a b ⊆ N.cylinderDomain := by
      rintro z ⟨_, hz⟩
      exact ⟨mem_univ _, ha.trans_lt hz.1, hz.2.trans_le hb⟩
    have heq : N.coordinate_map '' (univ ×ˢ Ioo a b) = N.region a b := by
      apply Subset.antisymm
      · rintro x ⟨z, hz, rfl⟩
        refine ⟨N.coordinate_map_mem (hdom hz), ?_⟩
        simpa only [N.coordinate_inverse_map z (hdom hz).2, mem_Ioo] using hz.2
      · intro x hx
        exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, N.coordinate_map_inverse hx.1⟩
    rw [← heq]
    exact (isConnected_univ.prod (isConnected_Ioo hab)).image _
      (N.coordinate_map_smooth.continuousOn.mono hdom)
  obtain ⟨a, haHalf⟩ := hminus.nonempty
  obtain ⟨b, hbHalf⟩ := hplus.nonempty
  have ha := hminusRegion haHalf
  have hb := hplusRegion hbHalf
  have hnegS : N.region (-N.epsilon⁻¹) t ⊆ Sᶜ := by
    intro x hx hxS
    exact ne_of_lt hx.2.2 (hmemS.mp hxS).2
  have hposS : N.region t N.epsilon⁻¹ ⊆ Sᶜ := by
    intro x hx hxS
    exact ne_of_gt hx.2.1 (hmemS.mp hxS).2
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  have hnegA : N.region (-N.epsilon⁻¹) t ⊆ A :=
    (hregionConnected _ _ ht.1 le_rfl ht.2.le).isPreconnected.subset_connectedComponentIn ha hnegS
  have hposB : N.region t N.epsilon⁻¹ ⊆ B :=
    (hregionConnected _ _ ht.2 ht.1.le le_rfl).isPreconnected.subset_connectedComponentIn hb hposS
  have hAc : IsConnected A := isConnected_connectedComponentIn_iff.mpr (hnegS ha)
  have hAS : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hBS : B ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hAK : A ⊆ connectedComponent N.center := by
    intro x hx
    have hc := hAc.subset_connectedComponent (hnegA ha) hx
    rwa [← connectedComponent_eq (N.m25_carrier_subset_connectedComponent ha.1)] at hc
  have hne : A ≠ B := by
    intro heq
    have havoid : ∀ x ∈ A, H x ≠ t := by
      intro x hx he
      exact hAS hx (hlevel (hAK hx) he)
    have hsign : t < H a := hAc.isPreconnected.lt_of_ne hH.continuousOn havoid
      ⟨b, heq.symm ▸ hposB hb, by rw [hinside b hb.1]; exact hb.2.1⟩ (hnegA ha)
    rw [hinside a ha.1] at hsign
    exact (not_lt_of_gt ha.2.2) hsign
  have hfront : S ⊆ frontier A ∩ frontier B := by
    intro x hx
    obtain ⟨q, rfl⟩ := hcentral.symm ▸ hx
    have hn := Poincare.Topology.collar_center_mem_closure_negative hr e q
    have hp := Poincare.Topology.collar_center_mem_closure_positive hr e q
    refine ⟨⟨closure_mono (hminusRegion.trans hnegA) hn, ?_⟩,
      ⟨closure_mono (hplusRegion.trans hposB) hp, ?_⟩⟩
    · intro hi
      exact hAS (interior_subset hi) (hcentral ▸ mem_range_self q)
    · intro hi
      exact hBS (interior_subset hi) (hcentral ▸ mem_range_self q)
  have hopp := Poincare.Topology.opposite_collar_components hr (N.isOpen_region _ _) e
    (a := a) (b := b)
  dsimp only at hopp
  rw [hcentral] at hopp
  have hout := hopp (hnegS ha) (hposS hb) hne hfront
  refine ⟨a, b, ha, hb, hnegA, hposB, hne, hout.1, hout.2.1, ?_⟩
  exact hout.2.2.2.2.trans
    (connectedComponent_eq (N.m25_carrier_subset_connectedComponent ha.1)).symm

end PoincareConjecture.EpsilonNeck
