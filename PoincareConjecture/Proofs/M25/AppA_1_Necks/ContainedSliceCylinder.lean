import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicSmoothChainChart
import PoincareConjecture.Proofs.M25.AppA_1_Necks.TrimmedChainCover
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RelativeSuccessorHeight
import PoincareConjecture.Proofs.M25.Mathlib.PositivePolar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyExtension
import Mathlib.Topology.Connected.TotallyDisconnected
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SupportedSliceGraph









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture



theorem BalancedNeckChain.exists_cylinder_chart_at_contained_slice :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      ∀ (R : EpsilonNeck g), R.epsilon = epsilon →
      ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
      let S : Set M := range (fun q : UnitTwoSphere => R.coordinate_map (q, s))
      S ⊆ U →
      ∃ P : OpenPartialHomeomorph M RoundCylinderSpace,
        P.source = U ∧ P.target = univ ×ˢ Ioo (-1 : ℝ) 1 ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P.symm P.target ∧
        P '' S = univ ×ˢ ({0} : Set ℝ) := by
  classical
  have hnormalize
      (ell upper : UnitTwoSphere → ℝ)
      (hell : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ell)
      (hupper : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper)
      (hl : ∀ q, ell q < 0) (hu : ∀ q, 0 < upper q) :
      ∃ T : OpenPartialHomeomorph RoundCylinderSpace RoundCylinderSpace,
        T.source = {z | ell z.1 < z.2 ∧ z.2 < upper z.1} ∧
        T.target = univ ×ˢ Ioo (-1 : ℝ) 1 ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          ∞ T T.source ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          ∞ T.symm T.target ∧
        (∀ q : UnitTwoSphere, T (q, 0) = (q, 0)) := by
    let V : Set RoundCylinderSpace := {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
    let W : Set RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 1
    let d : RoundCylinderSpace → ℝ := fun z =>
      (upper z.1 + ell z.1) * z.2 - 2 * ell z.1 * upper z.1
    let j : RoundCylinderSpace → ℝ := fun z =>
      (upper z.1 - ell z.1) - (upper z.1 + ell z.1) * z.2
    let F : RoundCylinderSpace → RoundCylinderSpace := fun z =>
      (z.1, (upper z.1 - ell z.1) * z.2 / d z)
    let G : RoundCylinderSpace → RoundCylinderSpace := fun z =>
      (z.1, -2 * ell z.1 * upper z.1 * z.2 / j z)
    have hw (q : UnitTwoSphere) : 0 < upper q - ell q :=
      sub_pos.mpr ((hl q).trans (hu q))
    have hd (z : RoundCylinderSpace) (hz : z ∈ V) : 0 < d z := by
      have h1 := mul_pos (sub_pos.mpr hz.2) (neg_pos.mpr (hl z.1))
      have h2 := mul_pos (sub_pos.mpr hz.1) (hu z.1)
      dsimp only [d]
      nlinarith only [h1, h2]
    have hj (z : RoundCylinderSpace) (hz : z ∈ W) : 0 < j z := by
      have h1 := mul_pos (show 0 < 1 + z.2 by linarith only [hz.2.1])
        (neg_pos.mpr (hl z.1))
      have h2 := mul_pos (sub_pos.mpr hz.2.2) (hu z.1)
      dsimp only [j]
      nlinarith only [h1, h2]
    have hFmem : MapsTo F V W := by
      intro z hz
      refine ⟨mem_univ _, ?_, ?_⟩
      · change -1 < (upper z.1 - ell z.1) * z.2 / d z
        apply (lt_div_iff₀ (hd z hz)).mpr
        have h := mul_pos (hu z.1) (sub_pos.mpr hz.1)
        dsimp only [d]
        nlinarith only [h]
      · change (upper z.1 - ell z.1) * z.2 / d z < 1
        apply (div_lt_iff₀ (hd z hz)).mpr
        have h := mul_pos (neg_pos.mpr (hl z.1)) (sub_pos.mpr hz.2)
        dsimp only [d]
        nlinarith only [h]
    have hGmem : MapsTo G W V := by
      intro z hz
      constructor
      · change ell z.1 < -2 * ell z.1 * upper z.1 * z.2 / j z
        apply (lt_div_iff₀ (hj z hz)).mpr
        have h := mul_pos (mul_pos (neg_pos.mpr (hl z.1)) (hw z.1))
          (show 0 < z.2 + 1 by linarith only [hz.2.1])
        dsimp only [j]
        nlinarith only [h]
      · change -2 * ell z.1 * upper z.1 * z.2 / j z < upper z.1
        apply (div_lt_iff₀ (hj z hz)).mpr
        have h := mul_pos (mul_pos (hu z.1) (hw z.1)) (sub_pos.mpr hz.2.2)
        dsimp only [j]
        nlinarith only [h]
    have hGF (z : RoundCylinderSpace) (hz : z ∈ V) : G (F z) = z := by
      refine Prod.ext (by rfl) ?_
      change -2 * ell z.1 * upper z.1 * ((upper z.1 - ell z.1) * z.2 / d z) /
        ((upper z.1 - ell z.1) -
          (upper z.1 + ell z.1) * ((upper z.1 - ell z.1) * z.2 / d z)) = z.2
      have hden : (upper z.1 - ell z.1) -
          (upper z.1 + ell z.1) * ((upper z.1 - ell z.1) * z.2 / d z) ≠ 0 :=
        (hj (F z) (hFmem hz)).ne'
      apply (div_eq_iff hden).mpr
      field_simp [(hd z hz).ne']
      dsimp only [d]
      ring
    have hFG (z : RoundCylinderSpace) (hz : z ∈ W) : F (G z) = z := by
      refine Prod.ext (by rfl) ?_
      change (upper z.1 - ell z.1) * (-2 * ell z.1 * upper z.1 * z.2 / j z) /
        ((upper z.1 + ell z.1) * (-2 * ell z.1 * upper z.1 * z.2 / j z) -
          2 * ell z.1 * upper z.1) = z.2
      have hden : (upper z.1 + ell z.1) * (-2 * ell z.1 * upper z.1 * z.2 / j z) -
          2 * ell z.1 * upper z.1 ≠ 0 := (hd (G z) (hGmem hz)).ne'
      apply (div_eq_iff hden).mpr
      field_simp [(hj z hz).ne']
      dsimp only [j]
      ring
    have hdc : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ d :=
      (((hupper.comp contMDiff_fst).add (hell.comp contMDiff_fst)).mul
        contMDiff_snd).sub
        ((contMDiff_const.mul (hell.comp contMDiff_fst)).mul
          (hupper.comp contMDiff_fst))
    have hjc : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ j :=
      ((hupper.comp contMDiff_fst).sub (hell.comp contMDiff_fst)).sub
        (((hupper.comp contMDiff_fst).add (hell.comp contMDiff_fst)).mul
          contMDiff_snd)
    have hFc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ F V :=
      contMDiff_fst.contMDiffOn.prodMk
        ((((hupper.comp contMDiff_fst).sub (hell.comp contMDiff_fst)).mul
          contMDiff_snd).contMDiffOn.div₀ hdc.contMDiffOn (fun z hz => (hd z hz).ne'))
    have hGc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ G W :=
      contMDiff_fst.contMDiffOn.prodMk
        ((((contMDiff_const.mul (hell.comp contMDiff_fst)).mul
          (hupper.comp contMDiff_fst)).mul contMDiff_snd).contMDiffOn.div₀
          hjc.contMDiffOn (fun z hz => (hj z hz).ne'))
    let T : OpenPartialHomeomorph RoundCylinderSpace RoundCylinderSpace := {
      toFun := F
      invFun := G
      source := V
      target := W
      map_source' := hFmem
      map_target' := hGmem
      left_inv' := hGF
      right_inv' := hFG
      open_source := (isOpen_lt (hell.continuous.comp continuous_fst)
        continuous_snd).inter (isOpen_lt continuous_snd
          (hupper.continuous.comp continuous_fst))
      open_target := isOpen_univ.prod isOpen_Ioo
      continuousOn_toFun := hFc.continuousOn
      continuousOn_invFun := hGc.continuousOn }
    refine ⟨T, rfl, rfl, hFc, hGc, ?_⟩
    intro q
    refine Prod.ext (by rfl) ?_
    change (upper q - ell q) * 0 / d (q, 0) = 0
    simp only [mul_zero, zero_div]
  obtain ⟨ec, hec, hcc, hchart⟩ :=
    BalancedNeckChain.exists_intrinsic_smooth_chain_partial_chart.{u}
  obtain ⟨et, het, _, htrim⟩ := BalancedNeckChain.exists_trimmed_cut_cover.{u}
  obtain ⟨es, hes, _, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := 1) (by norm_num)
  obtain ⟨eg, heg, _, hgraph⟩ := EpsilonNeck.exists_contained_slice_graph.{u}
  obtain ⟨er, her, _, hsuccessor⟩ :=
    EpsilonNeck.exists_relative_successor_height_continuity.{u}
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB : 0 < B0 := mul_pos (Real.sqrt_pos.2 (by norm_num)) (by positivity)
  let e0 := min ec (min et (min es (min eg (min er (1 / (1024 * (B0 + 1)))))))
  refine ⟨e0, lt_min hec (lt_min het (lt_min hes (lt_min heg
    (lt_min her (by positivity))))), (min_le_left _ _).trans hcc, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape heps hsep R hRe s hs
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L : ℝ := epsilon⁻¹
  let U : Set M := ⋃ j ∈ C.shape.active, (C.neck j).carrier
  let S : Set M := range (fun q : UnitTwoSphere => R.coordinate_map (q, s))
  change S ⊆ U → _
  intro hSU
  obtain ⟨hec', het', hes', heg', her', hnum⟩ :
      epsilon ≤ ec ∧ epsilon ≤ et ∧ epsilon ≤ es ∧ epsilon ≤ eg ∧
        epsilon ≤ er ∧ epsilon ≤ 1 / (1024 * (B0 + 1)) := by
    simpa only [e0, le_min_iff] using heps
  have hepos : 0 < epsilon := hRe ▸ R.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hmargin : 16 * B0 ≤ L / 64 := by
    have hd : 0 < 1024 * (B0 + 1) := by positivity
    have hh := (le_inv_comm₀ hepos hd).mp (by simpa only [one_div] using hnum)
    change 1024 * (B0 + 1) ≤ L at hh
    linarith
  have hactive (j : ℤ) : j ∈ C.shape.active ↔ a ≤ j ∧ j ≤ b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨j, hj⟩ := C.active_nonempty
    exact ((hactive j).mp hj).1.trans ((hactive j).mp hj).2
  have ha := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb := (hactive b).mpr ⟨hab, le_rfl⟩
  have hNU (j : ℤ) (hj : j ∈ C.shape.active) : (C.neck j).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨j, hj, hx⟩
  have hconn : IsConnected U := by
    have hfinite (j : ℤ) (haj : a ≤ j) (hjb : j ≤ b) :
        IsConnected (⋃ k ∈ Icc a j, (C.neck k).carrier) := by
      refine Int.leInduction (m := a) (motive := fun k _ => k ≤ b →
        IsConnected (⋃ l ∈ Icc a k, (C.neck l).carrier)) ?_ ?_ j haj hjb
      · intro _
        simpa only [Icc_self, biUnion_singleton] using (C.neck a).isConnected_carrier
      · intro k hak ih hk
        have hk0 := (hactive k).mpr ⟨hak, by omega⟩
        have hk1 := (hactive (k + 1)).mpr ⟨by omega, hk⟩
        have heq : (⋃ l ∈ Icc a (k + 1), (C.neck l).carrier) =
            (⋃ l ∈ Icc a k, (C.neck l).carrier) ∪ (C.neck (k + 1)).carrier := by
          ext x
          simp only [mem_iUnion, mem_Icc, mem_union]
          constructor
          · rintro ⟨l, hl, hx⟩
            by_cases he : l = k + 1
            · exact Or.inr (he ▸ hx)
            · exact Or.inl ⟨l, ⟨hl.1, by omega⟩, hx⟩
          · rintro (⟨l, hl, hx⟩ | hx)
            · exact ⟨l, ⟨hl.1, by omega⟩, hx⟩
            · exact ⟨k + 1, ⟨by omega, le_rfl⟩, hx⟩
        rw [heq]
        obtain ⟨x, hx, hxn⟩ := C.adjacent_overlap k hk0 hk1
        exact (ih (by omega)).union ⟨x, mem_iUnion₂.mpr ⟨k, ⟨hak, le_rfl⟩, hx⟩,
          hxn⟩ (C.neck (k + 1)).isConnected_carrier
    simpa only [U, hshape, ChainShape.active] using hfinite b hab le_rfl
  obtain ⟨H, _, hH, hK, _, hcuts, horder⟩ := C.exists_ordered_saturated_heights hsep
  have hUK (j : ℤ) (hj : j ∈ C.shape.active) {x : M} (hx : x ∈ U) :
      x ∈ connectedComponent (C.neck j).center := by
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    have hkj : connectedComponent (C.neck k).center =
        connectedComponent (C.neck j).center := hK k hk j hj
    exact hkj ▸ (C.neck k).m25_carrier_subset_connectedComponent hxk
  have hplateau (j : ℤ) (hj : j ∈ C.shape.active) {x : M} (hx : x ∈ U)
      (hn : x ∉ (C.neck j).carrier) : H j x = -L ∨ H j x = L :=
    (hH j hj).2.2.1 x ⟨hUK j hj hx, hn⟩
  have hdom (j : ℤ) (hj : j ∈ C.shape.active) {t : ℝ} (ht : t ∈ Ioo (-L) L) :
      t ∈ Ioo (-(C.neck j).epsilon⁻¹) (C.neck j).epsilon⁻¹ := by
    simpa only [C.epsilon_eq j hj] using ht
  have hpoint (j : ℤ) (hj : j ∈ C.shape.active) (q : UnitTwoSphere)
      {t : ℝ} (ht : t ∈ Ioo (-L) L) : H j ((C.neck j).coordinate_map (q, t)) = t := by
    rw [(hH j hj).2.1 _ ((C.neck j).coordinate_map_mem ⟨mem_univ _, hdom j hj ht⟩),
      (C.neck j).coordinate_inverse_map _ (hdom j hj ht)]
  have hunique (j : ℤ) (hj : j ∈ C.shape.active) (G : M → ℝ)
      (hGc : ContinuousOn G U)
      (hGin : ∀ x ∈ (C.neck j).carrier, G x = ((C.neck j).coordinate_inverse x).2)
      (hGout : ∀ x ∈ U, x ∉ (C.neck j).carrier → G x = -L ∨ G x = L) :
      EqOn G (H j) U := by
    have hm : MapsTo (fun x => G x - H j x) U ({-2 * L, 0, 2 * L} : Set ℝ) := by
      intro x hx
      by_cases hn : x ∈ (C.neck j).carrier
      · simp only [hGin x hn, (hH j hj).2.1 x hn, sub_self, mem_insert_iff,
          mem_singleton_iff, true_or, or_true]
      · rcases hGout x hx hn with hh | hh <;>
          rcases hplateau j hj hx hn with hk | hk <;>
          simp only [hh, hk, mem_insert_iff, mem_singleton_iff] <;> ring_nf <;> tauto
    have hc := hGc.sub (hH j hj).1.continuousOn
    have hcenter := (C.neck j).central_sphere_subset (C.neck j).center_on_central_sphere
    intro x hx
    have he := hconn.isPreconnected.constant_of_mapsTo
      (((finite_singleton (2 * L)).insert 0).insert (-2 * L)).isDiscrete
      hc hm hx (hNU j hj hcenter)
    change G x - H j x = G (C.neck j).center - H j (C.neck j).center at he
    rw [hGin _ hcenter, (hH j hj).2.1 _ hcenter, sub_self] at he
    exact sub_eq_zero.mp he
  let G0 : M → ℝ := fun x => if x ∈ (C.neck a).carrier then
    ((C.neck a).coordinate_inverse x).2 else L
  have hGa := hunique a ha G0 (C.continuousOn_initial_height_of_finite hshape).1
    (fun _ hx => if_pos hx) (fun _ _ hx => Or.inr (if_neg hx))
  have hlow {x : M} (hx : x ∈ U) : -L < H a x := by
    rw [← hGa hx]
    exact ((C.continuousOn_initial_height_of_finite hshape).2.1 x hx).1
  have hreceive (j : ℤ) (hj : j ∈ C.shape.active) (hn : j + 1 ∈ C.shape.active)
      {x : M} (hx : x ∈ (C.neck j).carrier) : H (j + 1) x < L / 2 := by
    apply (C.neck j).isConnected_carrier.isPreconnected.gt_of_ne
      (hH (j + 1) hn).1.continuousOn _ _ hx
    · intro y hy heq
      by_cases hyn : y ∈ (C.neck (j + 1)).carrier
      · have hh := (C.overlap_within_three_quarters j hj hn ⟨hy, hyn⟩).2.2.2
        rw [← (hH (j + 1) hn).2.1 y hyn] at hh
        exact hh.ne heq
      · rcases hplateau (j + 1) hn (hNU j hj hy) hyn with hm | hp <;> linarith
    · let q := ((C.neck (j + 1)).coordinate_inverse (C.neck (j + 1)).center).1
      have ht : -(3 * L / 4) ∈ Ioo (-L) L := ⟨by linarith, by linarith⟩
      have hy := (C.neck (j + 1)).coordinate_map_mem (z := (q, -(3 * L / 4)))
        ⟨mem_univ q, hdom _ hn ht⟩
      refine ⟨(C.neck (j + 1)).coordinate_map (q, -(3 * L / 4)),
        (C.overlap_contains_quarters j hj hn).2 ⟨hy, ?_⟩, ?_⟩
      · rw [(C.neck (j + 1)).coordinate_inverse_map _ (hdom _ hn ht)]
        exact ⟨by linarith, by linarith⟩
      · rw [hpoint _ hn q ht]
        linarith
  have hupp {x : M} (hx : x ∈ U) : H b x < L := by
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    by_cases he : j = b
    · subst j
      rw [(hH b hb).2.1 _ hxj]
      simpa only [C.epsilon_eq b hb] using ((C.neck b).coordinate_inverse_mem x hxj).2.2
    · have hjb : j < b := lt_of_le_of_ne ((hactive j).mp hj).2 he
      have haj := ((hactive j).mp hj).1
      have hn := (hactive (j + 1)).mpr ⟨by omega, by omega⟩
      have ht : 3 * L / 4 ∈ Ioo (-L) L := ⟨by linarith, by linarith⟩
      have hm : x ∈ connectedComponent (C.neck (j + 1)).center ∩
          (H (j + 1)) ⁻¹' Iio (3 * L / 4) :=
        ⟨hUK _ hn (hNU j hj hxj), by
          change H (j + 1) x < 3 * L / 4
          have hh := hreceive j hj hn hxj
          linarith⟩
      rw [← (hcuts (j + 1) hn _ ht).1] at hm
      by_cases hlast : j + 1 = b
      · subst b
        have hh := ((hcuts _ hn _ ht).1 ▸ hm).2
        change H (j + 1) x < 3 * L / 4 at hh
        linarith
      · have hh := (horder (j + 1) hn b hb (by omega)
          (3 * L / 4) ⟨by linarith, by linarith⟩
          (3 * L / 4) ⟨by linarith, by linarith⟩).1 (subset_closure hm)
        rw [(hcuts b hb _ ht).1] at hh
        have hlt : H b x < 3 * L / 4 := hh.2
        linarith
  have hsucc (j : ℤ) (hj : j ∈ C.shape.active) (hn : j + 1 ∈ C.shape.active)
      {x : M} (hx : x ∈ U) (hxn : x ∉ (C.neck (j + 1)).carrier) :
      H (j + 1) x = if H j x < 3 * L / 4 then -L else L := by
    let G : M → ℝ := fun y => if y ∈ (C.neck (j + 1)).carrier then
      ((C.neck (j + 1)).coordinate_inverse y).2
      else if H j y < 3 * L / 4 then -L else L
    have hc := hsuccessor (C.neck j) (C.neck (j + 1))
      (by simpa only [C.epsilon_eq j hj] using her')
      ((C.epsilon_eq _ hn).trans (C.epsilon_eq _ hj).symm)
      (by simpa only [C.epsilon_eq j hj] using (C.overlap_contains_quarters j hj hn).1)
      (by simpa only [C.epsilon_eq j hj] using C.overlap_within_three_quarters j hj hn)
      U (hNU j hj) (hNU _ hn) (H j) (hH j hj).1.continuousOn (hH j hj).2.1
      (by simpa only [C.epsilon_eq j hj] using fun y hy hn => hplateau j hj hy hn)
    have he := hunique (j + 1) hn G
      (by simpa only [G, L, C.epsilon_eq j hj] using hc)
      (fun _ hy => if_pos hy) (by
        intro y _ hy
        simp only [G, if_neg hy]
        split_ifs <;> simp)
    rw [← he hx]
    exact if_neg hxn
  obtain ⟨W, hWzero, hWdef, _, _, hWU, _⟩ :=
    htrim C het' hsep (23 * L / 32) (25 * L / 32)
      (by linarith) (by linarith) (by linarith)
  let q0 : UnitTwoSphere := (R.coordinate_inverse R.center).1
  let x0 := R.coordinate_map (q0, s)
  have hsR : s ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by simpa only [hRe] using hs
  have hx0R := R.coordinate_map_mem (z := (q0, s)) ⟨mem_univ q0, hsR⟩
  have hx0U : x0 ∈ U := hSU ⟨q0, rfl⟩
  change (⋃ i, W i) = U at hWU
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hWU.symm ▸ hx0U)
  have hi : i ∈ C.shape.active := by
    by_contra hn
    simp only [hWzero i hn, mem_empty_iff_false] at hxi
  have hxi' := hWdef i hi ▸ hxi
  have hxiN : x0 ∈ (C.neck i).carrier := hxi'.1.1
  have hscale2 (N N' : EpsilonNeck g) (heN : N.epsilon = epsilon)
      (heN' : N'.epsilon = epsilon) (hov : (N.carrier ∩ N'.carrier).Nonempty) :
      N'.scale < 2 * N.scale := by
    have hh := (hscale N N' (by simpa only [heN] using hes')
      (by simpa only [heN'] using hes') hov).2
    have hp := (abs_lt.mp hh).2
    have hd : N'.scale / N.scale < 2 := by linarith
    exact (div_lt_iff₀ N.scale_pos).mp hd
  have hRi := hscale2 (C.neck i) R (C.epsilon_eq i hi) hRe ⟨x0, hxiN, hx0R⟩
  have hosc (j : ℤ) (hj : j ∈ C.shape.active) (hr : R.scale ≤ 4 * (C.neck j).scale)
      (q : UnitTwoSphere) : |H j (R.coordinate_map (q, s)) - H j x0| ≤ L / 64 := by
    have hy := R.coordinate_map_mem (z := (q, s)) ⟨mem_univ q, hsR⟩
    have hd := R.edist_le_axial_add hy hx0R
    rw [R.coordinate_inverse_map _ hsR, R.coordinate_inverse_map _ hsR] at hd
    simp only [sub_self, abs_zero, zero_add, hRe] at hd
    have hp : Real.sqrt (1 + epsilon) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [hec'.trans hcc]⟩
    have hm : 1 / 2 ≤ Real.sqrt (1 - epsilon) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 1 - epsilon by linarith [hec'.trans hcc]),
        Real.sqrt_nonneg (1 - epsilon)]
    have hh := ((hH j hj).2.2.2 (R.coordinate_map (q, s)) x0).trans hd
    have hb0 : 0 ≤ R.scale * Real.sqrt (1 + epsilon) * B0 :=
      mul_nonneg (mul_nonneg R.scale_pos.le (Real.sqrt_nonneg _)) hB.le
    have hreal := (ENNReal.ofReal_le_ofReal_iff hb0).mp hh
    have hcoef : R.scale * Real.sqrt (1 + epsilon) ≤
        16 * ((C.neck j).scale * Real.sqrt (1 - epsilon)) := by
      nlinarith [mul_le_mul_of_nonneg_left hp R.scale_pos.le,
        mul_le_mul_of_nonneg_left hm (C.neck j).scale_pos.le]
    have hpos : 0 < (C.neck j).scale * Real.sqrt (1 - epsilon) :=
      mul_pos (C.neck j).scale_pos (by linarith)
    have hbd := mul_le_mul_of_nonneg_right hcoef hB.le
    have habs : |H j (R.coordinate_map (q, s)) - H j x0| ≤ 16 * B0 := by
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith only [hreal, hbd]
    exact habs.trans hmargin
  have hwhole (q : UnitTwoSphere) : R.coordinate_map (q, s) ∈ (C.neck i).carrier := by
    let y := R.coordinate_map (q, s)
    have hyU : y ∈ U := hSU ⟨q, rfl⟩
    have hiy : H i y < L := by
      by_cases hn : i + 1 ∈ C.shape.active
      · have hh := hxi'.2
        rw [if_pos hn, (hcuts i hi (25 * L / 32) ⟨by linarith, by linarith⟩).1] at hh
        have hbase : H i x0 < 25 * L / 32 := hh.2
        have ho := (abs_le.mp (hosc i hi (by linarith [(C.neck i).scale_pos]) q)).2
        change H i y - H i x0 ≤ L / 64 at ho
        linarith
      · have he : i = b := by have hai := (hactive i).mp hi; rw [hactive] at hn; omega
        exact he.symm ▸ hupp hyU
    by_contra hyn
    rcases hplateau i hi hyU hyn with hm | hp
    · by_cases hp : i - 1 ∈ C.shape.active
      · have hbase := hxi'.1.2
        rw [if_pos hp,
          (hcuts (i - 1) hp (23 * L / 32) ⟨by linarith, by linarith⟩).2.1] at hbase
        have hbase' : 23 * L / 32 < H (i - 1) x0 := hbase.2
        have hnext : i - 1 + 1 = i := by omega
        have hpi := hscale2 (C.neck (i - 1)) (C.neck i) (C.epsilon_eq _ hp)
          (C.epsilon_eq _ hi) (by
            have hov := C.adjacent_overlap _ hp (by simpa only [hnext] using hi)
            simpa only [hnext] using hov)
        have ho := (abs_le.mp (hosc (i - 1) hp (by linarith) q)).1
        have hpy : L / 2 < H (i - 1) y := by change -(L / 64) ≤ _ at ho; linarith
        by_cases hy : y ∈ (C.neck (i - 1)).carrier
        · apply hyn
          apply (show (C.neck (i - 1)).region (L / 2) L ⊆ (C.neck i).carrier by
            simpa only [hnext] using
              (C.overlap_contains_quarters _ hp (by simpa only [hnext] using hi)).1)
          refine ⟨hy, ?_, ?_⟩
          · rwa [← (hH _ hp).2.1 y hy]
          · simpa only [C.epsilon_eq _ hp] using ((C.neck _).coordinate_inverse_mem y hy).2.2
        · have hpyL : H (i - 1) y = L := (hplateau _ hp hyU hy).resolve_left (by intro h; linarith)
          have hh := hsucc (i - 1) hp (by simpa only [hnext] using hi)
            hyU (by simpa only [hnext] using hyn)
          rw [hnext, hpyL, if_neg (by linarith)] at hh
          linarith
      · have he : i = a := by have hai := (hactive i).mp hi; rw [hactive] at hp; omega
        have hh := hlow hyU
        rw [← he, hm] at hh
        exact lt_irrefl _ hh
    · exact hiy.ne hp
  obtain ⟨h, hhs, hhdom, hhrange⟩ := (hgraph (C.neck i) R
    (by simpa only [C.epsilon_eq i hi] using heg') (by simpa only [hRe] using heg')
    s hsR hwhole).1
  have hhL (q : UnitTwoSphere) : h q ∈ Ioo (-L) L := by
    simpa only [C.epsilon_eq i hi] using hhdom q
  let d : ℝ := 3 * L / 4
  have hd : d ∈ Ioo (-L) L := ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
  have hfinish (Ψ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞)
      (hsupp : ∃ K : Set M, IsCompact K ∧ K ⊆ (C.neck i).carrier ∧
        ∀ x, x ∉ K → Ψ x = x)
      (himage : Ψ '' S = range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, d))) :
      ∃ P : OpenPartialHomeomorph M RoundCylinderSpace,
        P.source = U ∧ P.target = univ ×ˢ Ioo (-1 : ℝ) 1 ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P.symm P.target ∧
        P '' S = univ ×ˢ ({0} : Set ℝ) := by
    obtain ⟨K, _, hKN, hfix⟩ := hsupp
    have hfixU (x : M) (hx : x ∉ U) : Ψ x = x :=
      hfix x (fun h => hx (hNU i hi (hKN h)))
    have hpres (x : M) : Ψ x ∈ U ↔ x ∈ U := by
      constructor
      · intro hx
        by_contra hn
        exact hn (hfixU x hn ▸ hx)
      · intro hx
        by_contra hn
        have he := Ψ.injective (hfixU (Ψ x) hn)
        exact hn (he.symm ▸ hx)
    obtain ⟨e, F, B, P0, hFi, _, he, _, _, hell, hupper, hbounds,
      hPsrc, hPtar, hPc, hPi, hlocal⟩ := hchart C hshape hec' i hi
    let ell0 : UnitTwoSphere → ℝ := fun q => (F a ((B a).symm q, -L)).2
    let upper0 : UnitTwoSphere → ℝ := fun q => (F b ((B b).symm q, L)).2
    have hls : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ell0 := by simpa only [hshape] using hell
    have hus : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper0 := by simpa only [hshape] using hupper
    have hbd (q : UnitTwoSphere) : ell0 q ≤ -L ∧ L ≤ upper0 q := by
      simpa only [hshape] using hbounds q
    have hPt : P0.target = {z | ell0 z.1 < z.2 ∧ z.2 < upper0 z.1} := by
      simpa only [hshape] using hPtar
    have heq (q : UnitTwoSphere) : (q, d) ∈ (e i).source := by
      rw [(he i hi).1]
      exact ⟨mem_univ _, hd⟩
    have hPe (q : UnitTwoSphere) : P0 (e i (q, d)) = (q, d) := by
      rw [(hlocal i).1 ((he i hi).2.2.2.2.2.2 q), hFi]
      change (e i).symm (e i (q, d)) = (q, d)
      exact (e i).left_inv (heq q)
    have hErange : range (fun q : UnitTwoSphere => e i (q, d)) =
        range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, d)) := by
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        have hx : e i (q, d) ∈ (C.neck i).carrier := (he i hi).2.1 ▸ (e i).map_source (heq q)
        have ht := (he i hi).2.2.2.2.1 (q, d) (heq q)
        refine ⟨((C.neck i).coordinate_inverse (e i (q, d))).1, ?_⟩
        have hz : (((C.neck i).coordinate_inverse (e i (q, d))).1, d) =
            (C.neck i).coordinate_inverse (e i (q, d)) := Prod.ext rfl ht.symm
        exact (congrArg (C.neck i).coordinate_map hz).trans
          ((C.neck i).coordinate_map_inverse hx)
      · rintro ⟨q, rfl⟩
        let x := (C.neck i).coordinate_map (q, d)
        have hx : x ∈ (e i).target := (he i hi).2.1.symm ▸
          (C.neck i).coordinate_map_mem ⟨mem_univ _, hdom i hi hd⟩
        have hz := (e i).map_target hx
        have ht := (he i hi).2.2.2.2.1 ((e i).symm x) hz
        rw [(e i).right_inv hx, (C.neck i).coordinate_inverse_map _ (hdom i hi hd)] at ht
        refine ⟨((e i).symm x).1, ?_⟩
        have hz' : (((e i).symm x).1, d) = (e i).symm x := Prod.ext rfl ht
        exact (congrArg (e i) hz').trans ((e i).right_inv hx)
    have hlevel : P0 '' range (fun q : UnitTwoSphere =>
        (C.neck i).coordinate_map (q, d)) = univ ×ˢ ({d} : Set ℝ) := by
      rw [← hErange, ← range_comp']
      simp only [hPe]
      ext z
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨mem_univ _, rfl⟩
      · rintro ⟨_, hz⟩
        exact ⟨z.1, Prod.ext rfl (mem_singleton_iff.mp hz).symm⟩
    let P1 := Ψ.toHomeomorph.toOpenPartialHomeomorph.trans P0
    have hP1s : P1.source = U := by
      ext x
      change (x ∈ univ ∧ Ψ x ∈ P0.source) ↔ x ∈ U
      simp only [mem_univ, true_and, hPsrc]
      exact hpres x
    have hP1t : P1.target = P0.target := by
      ext z
      change (z ∈ P0.target ∧ P0.symm z ∈ univ) ↔ z ∈ P0.target
      simp only [mem_univ, and_true]
    have hP1c : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P1 P1.source :=
      hPc.comp Ψ.contMDiff.contMDiffOn (fun _ hz => hz.2)
    have hP1i : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P1.symm P1.target :=
      Ψ.symm.contMDiff.comp_contMDiffOn (hPi.mono inter_subset_left)
    let T : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞ := {
      toFun := fun z => (z.1, z.2 - d)
      invFun := fun z => (z.1, z.2 + d)
      left_inv := fun z => Prod.ext rfl (sub_add_cancel _ _)
      right_inv := fun z => Prod.ext rfl (add_sub_cancel_right _ _)
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const) }
    let P2 := P1.transHomeomorph T.toHomeomorph
    have hP2s : P2.source = U := hP1s
    have hP2t : P2.target = {z | ell0 z.1 - d < z.2 ∧ z.2 < upper0 z.1 - d} := by
      ext z
      change T.symm z ∈ P1.target ↔ _
      rw [hP1t, hPt]
      change (ell0 z.1 < z.2 + d ∧ z.2 + d < upper0 z.1) ↔ _
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hP2c : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P2 P2.source :=
      T.contMDiff.comp_contMDiffOn hP1c
    have hP2i : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P2.symm P2.target :=
      hP1i.comp T.symm.contMDiff.contMDiffOn (fun _ hz => hz)
    obtain ⟨Z, hZs, hZt, hZc, hZi, hZzero⟩ := hnormalize
      (fun q => ell0 q - d) (fun q => upper0 q - d)
      (hls.sub contMDiff_const) (hus.sub contMDiff_const)
      (fun q => by have hb0 := (hbd q).1; dsimp [d]; linarith)
      (fun q => by have hb0 := (hbd q).2; dsimp [d]; linarith)
    have hmatch : P2.target = Z.source := hP2t.trans hZs.symm
    let P := P2.trans' Z hmatch
    refine ⟨P, hP2s, hZt, hZc.comp hP2c (fun _ hx => hmatch ▸ P2.map_source hx),
      hP2i.comp hZi (fun _ hz => hmatch.symm ▸ Z.map_target hz), ?_⟩
    have hP2level : P2 '' S = univ ×ˢ ({0} : Set ℝ) := by
      change (fun x => T (P0 (Ψ x))) '' S = _
      rw [← image_image (⇑T) (fun x => P0 (Ψ x)) S,
        ← image_image (⇑P0) (⇑Ψ) S, himage, hlevel]
      ext z
      constructor
      · rintro ⟨w, ⟨_, hw⟩, rfl⟩
        exact ⟨mem_univ _, by change w.2 - d = 0; rw [mem_singleton_iff.mp hw]; ring⟩
      · rintro ⟨_, hz⟩
        refine ⟨(z.1, d), ⟨mem_univ _, rfl⟩, Prod.ext rfl ?_⟩
        change d - d = z.2
        rw [sub_self, mem_singleton_iff.mp hz]
    change (fun x => Z (P2 x)) '' S = _
    rw [← image_image, hP2level]
    ext z
    constructor
    · rintro ⟨w, ⟨_, hw⟩, rfl⟩
      have hw0 : w = (w.1, 0) := Prod.ext rfl (mem_singleton_iff.mp hw)
      rw [hw0, hZzero]
      exact ⟨mem_univ _, rfl⟩
    · rintro ⟨_, hz⟩
      refine ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      rw [hZzero]
      exact Prod.ext rfl (mem_singleton_iff.mp hz).symm
  obtain ⟨Ψ, hsupport, hmove⟩ := (C.neck i).exists_supported_slice_graph_straightening
    h hhs hhdom d (hdom i hi hd)
  exact hfinish Ψ hsupport (by simpa only [hhrange] using hmove)

end PoincareConjecture
