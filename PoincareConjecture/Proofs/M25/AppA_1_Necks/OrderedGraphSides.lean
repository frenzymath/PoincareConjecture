import PoincareConjecture.Proofs.M25.AppA_1_Necks.RetainedLevelComponents
import PoincareConjecture.Proofs.M25.AppA_1_Necks.AdjacentCutCover
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}




theorem graph_sides_in_height_preserving_chart
    (N N' : EpsilonNeck g) (hsep : N.IsSeparating)
    (hquarter : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier)
    (hoverlap : N.carrier ∩ N'.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        N'.region (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2))
    (j : OpenPartialHomeomorph RoundCylinderSpace M)
    (hjsource : j.source = N'.cylinderDomain)
    (hjtarget : j.target = N'.carrier)
    (hjheight : ∀ z ∈ N'.cylinderDomain,
      (N'.coordinate_inverse (j z)).2 = z.2)
    {t : ℝ} (ht : t ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hfdom : ∀ q, f q ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hgraph : range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) =
      range (fun q : UnitTwoSphere => j (q, f q))) :
    (∀ q, f q ∈ Ioo (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2)) ∧
      let q₀ := (N.coordinate_inverse N.center).1
      let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
      let A := connectedComponentIn Sᶜ
        (N.coordinate_map (q₀, (t - N.epsilon⁻¹) / 2))
      let B := connectedComponentIn Sᶜ
        (N.coordinate_map (q₀, (t + N.epsilon⁻¹) / 2))
      ∀ x ∈ N'.carrier,
        (x ∈ A ↔ (j.symm x).2 < f (j.symm x).1) ∧
        (x ∈ B ↔ f (j.symm x).1 < (j.symm x).2) := by
  classical
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hL' : 0 < N'.epsilon⁻¹ := inv_pos.mpr N'.epsilon_pos
  have ht0 : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨H, hH, hinside, houtside, _, hnewOutside, _, _⟩ :=
    N.exists_adjacent_saturated_cut_cover N' hsep hquarter
      (fun _ hx => (hoverlap hx).1)
  let q₀ := (N.coordinate_inverse N.center).1
  let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, t))
  let a := N.coordinate_map (q₀, (t - N.epsilon⁻¹) / 2)
  let b := N.coordinate_map (q₀, (t + N.epsilon⁻¹) / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  have hmemS {x : M} : x ∈ S ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = t := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨N.coordinate_map_mem ⟨mem_univ _, ht0⟩,
        congrArg Prod.snd (N.coordinate_inverse_map _ ht0)⟩
    · rintro ⟨hx, he⟩
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      rw [← he]
      exact N.coordinate_map_inverse hx
  have hlevel {x : M} (hx : x ∈ connectedComponent N.center) : H x = t ↔ x ∈ S := by
    constructor
    · intro he
      by_cases hxc : x ∈ N.carrier
      · exact hmemS.mpr ⟨hxc, (hinside x hxc).symm.trans he⟩
      · rcases houtside x ⟨hx, hxc⟩ with hn | hp
        · exact False.elim (ne_of_lt ht0.1 (hn.symm.trans he))
        · exact False.elim (ne_of_gt ht0.2 (hp.symm.trans he))
    · intro hs
      exact (hinside x (hmemS.mp hs).1).trans (hmemS.mp hs).2
  have hquarterPoint (r : ℝ) (hr : r ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
      N.coordinate_map (q₀, r) ∈ N.carrier ∩ N'.carrier := by
    have hr0 : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨by linarith [hr.1], hr.2⟩
    have hm : N.coordinate_map (q₀, r) ∈ N.carrier :=
      N.coordinate_map_mem ⟨mem_univ _, hr0⟩
    refine ⟨hm, hquarter ⟨hm, ?_⟩⟩
    simpa only [N.coordinate_inverse_map (q₀, r) hr0, mem_Ioo] using hr
  have hnewK : N'.carrier ⊆ connectedComponent N.center := by
    have hp := hquarterPoint (3 * N.epsilon⁻¹ / 4) ⟨by linarith, by linarith⟩
    intro x hx
    have hc := N'.isConnected_carrier.subset_connectedComponent hp.2 hx
    rwa [← connectedComponent_eq (N.m25_carrier_subset_connectedComponent hp.1)] at hc
  have hah : (t - N.epsilon⁻¹) / 2 ∈ Ioo (-N.epsilon⁻¹) t := by
    constructor <;> linarith [ht0.1]
  have hbh : (t + N.epsilon⁻¹) / 2 ∈ Ioo t N.epsilon⁻¹ := by
    constructor <;> linarith [ht.2]
  have hadom : (t - N.epsilon⁻¹) / 2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨hah.1, hah.2.trans ht.2⟩
  have hbdom : (t + N.epsilon⁻¹) / 2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨ht0.1.trans hbh.1, hbh.2⟩
  have ha : a ∈ N.region (-N.epsilon⁻¹) t := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hadom⟩, ?_⟩
    simpa only [a, N.coordinate_inverse_map (q₀, (t - N.epsilon⁻¹) / 2) hadom,
      mem_Ioo] using hah
  have hb : b ∈ N.region t N.epsilon⁻¹ := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hbdom⟩, ?_⟩
    simpa only [b, N.coordinate_inverse_map (q₀, (t + N.epsilon⁻¹) / 2) hbdom,
      mem_Ioo] using hbh
  obtain ⟨a₁, b₁, _, _, hneg, hpos, _, _, _, hcover⟩ :=
    N.exists_opposite_retained_components hsep ht0
  have hAe : connectedComponentIn Sᶜ a₁ = A := connectedComponentIn_eq (hneg ha)
  have hBe : connectedComponentIn Sᶜ b₁ = B := connectedComponentIn_eq (hpos hb)
  change N.region (-N.epsilon⁻¹) t ⊆ connectedComponentIn Sᶜ a₁ at hneg
  change N.region t N.epsilon⁻¹ ⊆ connectedComponentIn Sᶜ b₁ at hpos
  change connectedComponentIn Sᶜ a₁ ∪ S ∪ connectedComponentIn Sᶜ b₁ =
    connectedComponent N.center at hcover
  rw [hAe] at hneg
  rw [hBe] at hpos
  rw [hAe, hBe] at hcover
  have hAK : A ⊆ connectedComponent N.center := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inl hx)
  have hBK : B ⊆ connectedComponent N.center := by
    intro x hx
    rw [← hcover]
    exact Or.inr hx
  have hAavoid : ∀ x ∈ A, H x ≠ t := by
    intro x hx he
    exact connectedComponentIn_subset Sᶜ a hx ((hlevel (hAK hx)).mp he)
  have hBavoid : ∀ x ∈ B, H x ≠ t := by
    intro x hx he
    exact connectedComponentIn_subset Sᶜ b hx ((hlevel (hBK hx)).mp he)
  have hAsign : ∀ x ∈ A, H x < t := by
    intro x hx
    apply isPreconnected_connectedComponentIn.gt_of_ne hH.continuousOn hAavoid _ hx
    refine ⟨a, hneg ha, ?_⟩
    rw [hinside a ha.1]
    exact ha.2.2
  have hBsign : ∀ x ∈ B, t < H x := by
    intro x hx
    apply isPreconnected_connectedComponentIn.lt_of_ne hH.continuousOn hBavoid _ hx
    refine ⟨b, hpos hb, ?_⟩
    rw [hinside b hb.1]
    exact hb.2.1
  have hAmem {x : M} (hx : x ∈ connectedComponent N.center) : x ∈ A ↔ H x < t := by
    refine ⟨hAsign x, ?_⟩
    intro hs
    have hxK := hx
    rw [← hcover] at hx
    rcases hx with (hxa | hxs) | hxb
    · exact hxa
    · exact False.elim (hs.ne ((hlevel hxK).mpr hxs))
    · exact False.elim (lt_asymm hs (hBsign x hxb))
  have hBmem {x : M} (hx : x ∈ connectedComponent N.center) : x ∈ B ↔ t < H x := by
    refine ⟨hBsign x, ?_⟩
    intro hs
    have hxK := hx
    rw [← hcover] at hx
    rcases hx with (hxa | hxs) | hxb
    · exact False.elim (lt_asymm hs (hAsign x hxa))
    · exact False.elim (hs.ne ((hlevel hxK).mpr hxs).symm)
    · exact hxb
  have hjdom {z : RoundCylinderSpace} (hz : z ∈ N'.cylinderDomain) : z ∈ j.source :=
    hjsource.symm ▸ hz
  have hjmem {z : RoundCylinderSpace} (hz : z ∈ N'.cylinderDomain) : j z ∈ N'.carrier :=
    hjtarget ▸ j.map_source (hjdom hz)
  have hjinv {x : M} (hx : x ∈ N'.carrier) : j.symm x ∈ N'.cylinderDomain :=
    hjsource ▸ j.map_target (hjtarget.symm ▸ hx)
  have hfbound : ∀ q, f q ∈ Ioo (-N'.epsilon⁻¹) (N'.epsilon⁻¹ / 2) := by
    intro q
    have hqdom : (q, f q) ∈ N'.cylinderDomain := ⟨mem_univ _, hfdom q⟩
    have hqs : j (q, f q) ∈ S := by
      change j (q, f q) ∈ range (fun p => N.coordinate_map (p, t))
      rw [hgraph]
      exact mem_range_self q
    have hq := (hoverlap ⟨(hmemS.mp hqs).1, hjmem hqdom⟩).2.2.2
    rw [hjheight _ hqdom] at hq
    exact ⟨(hfdom q).1, hq⟩
  let Dminus : Set RoundCylinderSpace := {z | -N'.epsilon⁻¹ < z.2 ∧ z.2 < f z.1}
  let Dplus : Set RoundCylinderSpace := {z | f z.1 < z.2 ∧ z.2 < N'.epsilon⁻¹}
  let Wminus := j '' Dminus
  let Wplus := j '' Dplus
  have hminusD : Dminus ⊆ N'.cylinderDomain := by
    intro z hz
    exact ⟨mem_univ _, hz.1, hz.2.trans (hfdom z.1).2⟩
  have hplusD : Dplus ⊆ N'.cylinderDomain := by
    intro z hz
    exact ⟨mem_univ _, (hfdom z.1).1.trans hz.1, hz.2⟩
  have hminus : IsConnected Wminus :=
    (isConnected_between_continuous_graphs continuous_const hf (fun q => (hfdom q).1)).image
      j (j.continuousOn.mono (fun _ hz => hjdom (hminusD hz)))
  have hplus : IsConnected Wplus :=
    (isConnected_between_continuous_graphs hf continuous_const (fun q => (hfdom q).2)).image
      j (j.continuousOn.mono (fun _ hz => hjdom (hplusD hz)))
  have hminusU : Wminus ⊆ N'.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact hjmem (hminusD hz)
  have hplusU : Wplus ⊆ N'.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact hjmem (hplusD hz)
  have hmemMinus {x : M} (hx : x ∈ N'.carrier) :
      x ∈ Wminus ↔ (j.symm x).2 < f (j.symm x).1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [j.left_inv (hjdom (hminusD hz))] using hz.2
    · intro hs
      exact ⟨j.symm x, ⟨(hjinv hx).2.1, hs⟩, j.right_inv (hjtarget.symm ▸ hx)⟩
  have hmemPlus {x : M} (hx : x ∈ N'.carrier) :
      x ∈ Wplus ↔ f (j.symm x).1 < (j.symm x).2 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [j.left_inv (hjdom (hplusD hz))] using hz.1
    · intro hs
      exact ⟨j.symm x, ⟨hs, (hjinv hx).2.2⟩, j.right_inv (hjtarget.symm ▸ hx)⟩
  have hequal {x : M} (hx : x ∈ N'.carrier) :
      H x = t ↔ (j.symm x).2 = f (j.symm x).1 := by
    rw [hlevel (hnewK hx), show S = range (fun q => j (q, f q)) from hgraph]
    constructor
    · rintro ⟨q, rfl⟩
      rw [j.left_inv (hjdom ⟨mem_univ _, hfdom q⟩)]
    · intro hs
      refine ⟨(j.symm x).1, ?_⟩
      change j ((j.symm x).1, f (j.symm x).1) = x
      rw [← hs]
      exact j.right_inv (hjtarget.symm ▸ hx)
  have hminusNe : ∀ x ∈ Wminus, H x ≠ t := by
    intro x hx heq
    exact (ne_of_lt ((hmemMinus (hminusU hx)).mp hx))
      ((hequal (hminusU hx)).mp heq)
  have hplusNe : ∀ x ∈ Wplus, H x ≠ t := by
    intro x hx heq
    exact (ne_of_gt ((hmemPlus (hplusU hx)).mp hx))
      ((hequal (hplusU hx)).mp heq)
  let q₁ := (N'.coordinate_inverse N'.center).1
  let yplus := j (q₁, 3 * N'.epsilon⁻¹ / 4)
  have hypdom : (q₁, 3 * N'.epsilon⁻¹ / 4) ∈ N'.cylinderDomain := by
    refine ⟨mem_univ _, ?_, ?_⟩ <;> linarith
  have hypnew : yplus ∈ N'.carrier := hjmem hypdom
  have hypnot : yplus ∉ N.carrier := by
    intro hy
    have h := (hoverlap ⟨hy, hypnew⟩).2.2.2
    rw [hjheight _ hypdom] at h
    dsimp only at h
    linarith
  have hypplus : yplus ∈ Wplus := by
    refine ⟨(q₁, 3 * N'.epsilon⁻¹ / 4), ⟨?_, ?_⟩, rfl⟩
    · have h := (hfbound q₁).2
      dsimp only
      linarith
    · dsimp only
      linarith
  have hplusSign : ∀ x ∈ Wplus, t < H x := by
    intro x hx
    apply hplus.isPreconnected.lt_of_ne hH.continuousOn hplusNe _ hx
    exact ⟨yplus, hypplus, by rw [hnewOutside yplus ⟨hypnew, hypnot⟩]; exact ht.2⟩
  let r := (N.epsilon⁻¹ / 2 + t) / 2
  have hr : r ∈ Ioo (N.epsilon⁻¹ / 2) t := by
    dsimp only [r]
    constructor <;> linarith [ht.1]
  have hrdom : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨by linarith [hr.1], hr.2.trans ht.2⟩
  have hymn := hquarterPoint r ⟨hr.1, hr.2.trans ht.2⟩
  have hymH : H (N.coordinate_map (q₀, r)) < t := by
    rw [hinside _ hymn.1, N.coordinate_inverse_map _ hrdom]
    exact hr.2
  have hymminus : N.coordinate_map (q₀, r) ∈ Wminus := by
    apply (hmemMinus hymn.2).mpr
    rcases lt_trichotomy (j.symm (N.coordinate_map (q₀, r))).2
        (f (j.symm (N.coordinate_map (q₀, r))).1) with hlo | heq | hhi
    · exact hlo
    · exact False.elim (hymH.ne ((hequal hymn.2).mpr heq))
    · exact False.elim (lt_asymm hymH (hplusSign _ ((hmemPlus hymn.2).mpr hhi)))
  have hminusSign : ∀ x ∈ Wminus, H x < t := by
    intro x hx
    exact hminus.isPreconnected.gt_of_ne hH.continuousOn hminusNe
      ⟨N.coordinate_map (q₀, r), hymminus, hymH⟩ hx
  refine ⟨hfbound, ?_⟩
  change ∀ x ∈ N'.carrier,
    (x ∈ A ↔ (j.symm x).2 < f (j.symm x).1) ∧
    (x ∈ B ↔ f (j.symm x).1 < (j.symm x).2)
  intro x hx
  have hlow (hs : (j.symm x).2 < f (j.symm x).1) : H x < t :=
    hminusSign x ((hmemMinus hx).mpr hs)
  have hhigh (hs : f (j.symm x).1 < (j.symm x).2) : t < H x :=
    hplusSign x ((hmemPlus hx).mpr hs)
  rw [hAmem (hnewK hx), hBmem (hnewK hx)]
  constructor
  · refine ⟨?_, hlow⟩
    intro hs
    rcases lt_trichotomy (j.symm x).2 (f (j.symm x).1) with hlo | heq | hhi
    · exact hlo
    · exact False.elim (hs.ne ((hequal hx).mpr heq))
    · exact False.elim (lt_asymm hs (hhigh hhi))
  · refine ⟨?_, hhigh⟩
    intro hs
    rcases lt_trichotomy (j.symm x).2 (f (j.symm x).1) with hlo | heq | hhi
    · exact False.elim (lt_asymm hs (hlow hlo))
    · exact False.elim (hs.ne ((hequal hx).mpr heq).symm)
    · exact hhi

end PoincareConjecture.EpsilonNeck
