import PoincareConjecture.Proofs.M25.Mathlib.CompactFrontierUniqueness
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoCapCuts
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapStandardEnd
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.BufferedCollar
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesCompactSide












set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capCertificates_exists_second_buffered_ball_chart
    (hS : SchoenfliesService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (hkind2 : C2.model_kind = CapModelKind.euclidean)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    let +nondep U2 : TopologicalSpace.Opens M :=
      { carrier := C2.carrier, is_open' := C2.carrier_open }
    let L := C1.epsilon⁻¹
    let Y := C1.carrier ∪ C2.carrier
    let N := C1
    let K : ℝ → Set M := fun s => C1.carrier \ N.region s L
    let V : ℝ → Set M := fun s => interior (K s)
    let W : ℝ → Set M := fun s => Y \ K s
    ∃ v ∈ Ioo (-L) L, (Y \ C2.carrier) ⊆ V v ∧
      let +nondep c := (v + L) / 2
      let +nondep h := (L - v) / 4
      let a := c - h * (3 / 4)
      let b := c - h * (1 / 2)
      0 < h ∧ v < c - h ∧ c + h < L ∧
      v < a ∧ a < b ∧ b < L ∧
      ∃ (Phi2 : Diffeomorph (𝓡 3) (𝓡 3) U2 E3 ∞)
        (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) U2)
        (S : SchoenfliesData
          (fun p : UnitTwoSphere × ℝ => (Phi2 : U2 → E3)
            ((e : UnitTwoSphere × ℝ → U2) (p.1, c + h * p.2))) (1 / 4))
        (J : OpenPartialHomeomorph M E3),
        e.source = univ ×ˢ Ioo v L ∧
        e.target = (Subtype.val : U2 → M) ⁻¹' N.region v L ∧
        (∀ z ∈ e.source, (e z).val = N.coordinate_map z) ∧
        (∀ x : U2, e.symm x = N.coordinate_inverse x.val) ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
        IsCollarEmbedding (fun p => Phi2 (e (p.1, c + h * p.2))) ∧
        S.side = -1 ∧
        (∀ t ∈ Ico (1 / 4 : ℝ) 1,
          Phi2 '' ((Subtype.val : U2 → M) ⁻¹' (Y \ V (c - h * t))) =
              S.chart '' closedBall 0 (S.radial t) ∧
          Phi2 '' ((Subtype.val : U2 → M) ⁻¹' W (c - h * t)) =
              S.chart '' ball 0 (S.radial t)) ∧
        J.source = W a ∧ J.target = ball 0 (S.radial (3 / 4)) ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ J J.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ J.symm J.target ∧
        (J.symm : E3 → M) = (fun z => (Phi2.symm (S.chart z)).val) ∧
        (∀ x : U2, x.val ∈ J.source → S.chart (J x.val) = Phi2 x) ∧
        V b ∪ J.source = Y ∧ V b ∩ J.source = N.region a b ∧
        J '' (N.region a b) =
          {z : E3 | S.radial (1 / 2) < ‖z‖ ∧ ‖z‖ < S.radial (3 / 4)} ∧
        (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Ico (1 / 4) (3 / 4) →
          N.coordinate_map (q, c - h * t) ∈ J.source ∧
          J (N.coordinate_map (q, c - h * t)) =
            S.radial t • (S.boundary_map q).val) ∧
        (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 2) (3 / 4) →
          J.symm (S.radial t • (S.boundary_map q).val) =
            N.coordinate_map (q, c - h * t)) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let U2 : TopologicalSpace.Opens M :=
    { carrier := C2.carrier, is_open' := C2.carrier_open }
  let L := C1.epsilon⁻¹
  let Y := C1.carrier ∪ C2.carrier
  let N := C1
  let K : ℝ → Set M := fun s => C1.carrier \ N.region s L
  let V : ℝ → Set M := fun s => interior (K s)
  let W : ℝ → Set M := fun s => Y \ K s
  let Q : ℝ → Set M := fun s => Y \ V s
  let Sigma : ℝ → Set M := fun s => N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ))
  have hbuffer := capCertificates_exists_buffered_cut_cover C1 C2 hcompact
  obtain ⟨v, hv, haway, hcuts⟩ := hbuffer
  change v ∈ Ioo (-L) L at hv
  change (Y \ C2.carrier) ⊆ V v at haway
  let c := (v + L) / 2
  let h := (L - v) / 4
  let a := c - h * (3 / 4)
  let b := c - h * (1 / 2)
  have hh : 0 < h := by dsimp only [h]; linarith [hv.2]
  have hleft : v < c - h := by dsimp only [c, h]; linarith [hv.2]
  have hright : c + h < L := by dsimp only [c, h]; linarith [hv.2]
  have hva : v < a := by dsimp only [a]; linarith
  have hab : a < b := by dsimp only [a, b]; linarith
  have hbL : b < L := by dsimp only [b]; linarith
  refine ⟨v, hv, haway, hh, hleft, hright, hva, hab, hbL, ?_⟩
  have hdom {s : ℝ} (hs : s ∈ Ioo v L) :
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact ⟨hv.1.trans hs.1, hs.2⟩
  have hstrip {z : UnitTwoSphere × ℝ} (hz : z ∈ univ ×ˢ Ioo v L) :
      N.coordinate_map z ∈ C2.carrier := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hslab⟩ :=
      hcuts ((v + z.2) / 2) ((z.2 + L) / 2)
        (by linarith [hz.2.1]) (by linarith [hz.2.1, hz.2.2])
        (by linarith [hz.2.2])
    exact hslab ⟨z, ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩, rfl⟩
  have hcut {s : ℝ} (hs : s ∈ Ioo v L) :
      IsOpen (W s) ∧ closure (W s) = Q s ∧ interior (Q s) = W s ∧
      IsCompact (Q s) ∧ Q s ⊆ C2.carrier ∧ frontier (Q s) = Sigma s := by
    obtain ⟨_, ho, hc, hi, hq, hsub, hf, _, _, _, _, _⟩ :=
      hcuts s ((s + L) / 2) hs.1 (by linarith [hs.2]) (by linarith [hs.2])
    refine ⟨ho, hc, hi, hq, hsub, ?_⟩
    rw [hq.isClosed.frontier_eq, hi, ← hc, ← ho.frontier_eq]
    exact hf
  let R := C2.model_equivalence
  let : TopologicalSpace R.model := R.model_topology
  let : ChartedSpace E3 R.model := R.model_charted
  let : IsManifold (𝓡 3) ∞ R.model := R.model_manifold
  obtain ⟨F, _, _⟩ := capModelEquivalence_exists_carrierDiffeomorph U2 R
  have hstd : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) R.model E3 ∞) := by
    have hs := R.standard_smooth
    split at hs
    · exact hs
    · simp_all only [reduceCtorEq]
  obtain ⟨D0⟩ := hstd
  let Phi2 := F.trans D0
  let hU2 : Nonempty U2 := ⟨Phi2.symm 0⟩
  let f := N.end_chart.symm
  let e0 : OpenPartialHomeomorph (UnitTwoSphere × ℝ) U2 := (f.subtypeRestr hU2).symm
  let e := e0.restrOpen (univ ×ˢ Ioo v L) (isOpen_univ.prod isOpen_Ioo)
  have he0 {z : UnitTwoSphere × ℝ} (hz : z ∈ univ ×ˢ Ioo v L) : z ∈ e0.source := by
    change z ∈ (f.subtypeRestr hU2).target
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
      U2.openPartialHomeomorphSubtypeCoe_target]
    change z ∈ N.end_chart.source ∧ N.coordinate_map z ∈ C2.carrier
    rw [N.end_chart_source]
    exact ⟨⟨mem_univ _, hdom hz.2⟩, hstrip hz⟩
  have hes : e.source = univ ×ˢ Ioo v L := inter_eq_right.mpr (fun _ hz => he0 hz)
  have hef (z : UnitTwoSphere × ℝ) (hz : z ∈ e.source) :
      (e z).val = N.coordinate_map z :=
    f.subtypeRestr_symm_apply hU2 (he0 (hes ▸ hz))
  have hei (x : U2) : e.symm x = N.coordinate_inverse x.val := rfl
  have het : e.target = (Subtype.val : U2 → M) ⁻¹' N.region v L := by
    ext x
    change (x ∈ e0.target ∧ e0.symm x ∈ univ ×ˢ Ioo v L) ↔ _
    rw [show e0.target = (Subtype.val : U2 → M) ⁻¹' N.end_chart.target from
      f.subtypeRestr_source hU2]
    change (x.val ∈ N.end_chart.target ∧ N.coordinate_inverse x.val ∈ univ ×ˢ Ioo v L) ↔ _
    simp only [mem_prod, mem_univ, true_and, mem_preimage]
    rfl
  have he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source := by
    have hm : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map e.source :=
      N.coordinate_map_smooth.mono (fun z hz => ⟨mem_univ _, hdom ((hes ▸ hz).2)⟩)
    have hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (Subtype.val ∘ e) e.source := hm.congr hef
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U2 e e.source z).mp (hc z hz)
  have heinv : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
    exact N.coordinate_inverse_smooth.comp contMDiff_subtype_val.contMDiffOn
      (fun x hx => (show x ∈ (Subtype.val : U2 → M) ⁻¹' N.region v L from het ▸ hx).1)
  have hpsi := isCollarEmbedding_of_buffered_chart Phi2 e hes he heinv hh hleft hright
  obtain ⟨S⟩ := hS _ hpsi (1 / 4) (by norm_num) (by norm_num)
  have hheight (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      c + h * (S.side * t) ∈ Ioo v L := by
    rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
    · rw [hs, one_mul]
      constructor <;> nlinarith [ht.1, ht.2]
    · rw [hs, neg_one_mul]
      constructor <;> nlinarith [ht.1, ht.2]
  have hvalOpen : IsOpenMap (Subtype.val : U2 → M) :=
    C2.carrier_open.isOpenEmbedding_subtypeVal.isOpenMap
  have hQimage (s : ℝ) (hs : s ∈ Ioo v L) :
      (Subtype.val : U2 → M) '' ((Subtype.val : U2 → M) ⁻¹' Q s) = Q s := by
    ext x
    exact ⟨fun ⟨y, hy, heq⟩ => heq ▸ hy,
      fun hx => ⟨⟨x, (hcut hs).2.2.2.2.1 hx⟩, hx, rfl⟩⟩
  have hPhiInterior (T : Set M) :
      interior (Phi2 '' ((Subtype.val : U2 → M) ⁻¹' T)) =
        Phi2 '' ((Subtype.val : U2 → M) ⁻¹' interior T) := by
    have hh := Phi2.toHomeomorph.image_interior ((Subtype.val : U2 → M) ⁻¹' T)
    rw [← hvalOpen.preimage_interior_eq_interior_preimage continuous_subtype_val] at hh
    exact hh.symm
  have hPhiFrontier (T : Set M) :
      frontier (Phi2 '' ((Subtype.val : U2 → M) ⁻¹' T)) =
        Phi2 '' ((Subtype.val : U2 → M) ⁻¹' frontier T) := by
    have hh := Phi2.toHomeomorph.image_frontier ((Subtype.val : U2 → M) ⁻¹' T)
    rw [← hvalOpen.preimage_frontier_eq_frontier_preimage continuous_subtype_val] at hh
    exact hh.symm
  have hballs (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      Phi2 '' ((Subtype.val : U2 → M) ⁻¹' Q (c + h * (S.side * t))) =
        S.chart '' closedBall 0 (S.radial t) := by
    let s := c + h * (S.side * t)
    have hs : s ∈ Ioo v L := hheight t ht
    obtain ⟨_, _, hi, hQ, hQC, hfront⟩ := hcut hs
    have hP : IsCompact (Phi2 '' ((Subtype.val : U2 → M) ⁻¹' Q s)) := by
      apply IsCompact.image _ Phi2.continuous
      apply Subtype.isCompact_iff.mpr
      rw [hQimage s hs]
      exact hQ
    have hPi : (interior (Phi2 '' ((Subtype.val : U2 → M) ⁻¹' Q s))).Nonempty := by
      rw [hPhiInterior, hi]
      let q := (N.coordinate_inverse N.endCenter).1
      let z : UnitTwoSphere × ℝ := (q, (s + L) / 2)
      have hz : z ∈ univ ×ˢ Ioo v L :=
        ⟨mem_univ _, by dsimp only [z]; linarith [hs.1, hs.2],
          by dsimp only [z]; linarith [hs.2]⟩
      let x : U2 := ⟨N.coordinate_map z, hstrip hz⟩
      refine ⟨Phi2 x, x, ?_, rfl⟩
      refine ⟨Or.inl (C1.end_chart_target_subset
        (N.coordinate_map_mem ⟨mem_univ _, hdom hz.2⟩)), ?_⟩
      intro hxK
      apply hxK.2
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdom hz.2⟩, ?_⟩
      rw [N.coordinate_inverse_map z (hdom hz.2)]
      dsimp only [z]
      constructor <;> linarith [hs.2]
    have hBi : IsPreconnected (interior (S.chart '' closedBall 0 (S.radial t))) := by
      rw [S.interior_chart_closedBall ht]
      exact isPreconnected_ball.image S.chart
        (S.chart_smooth.continuousOn.mono (ball_subset_ball (S.radial_lt t ht).le))
    have hfrontEq : frontier (Phi2 '' ((Subtype.val : U2 → M) ⁻¹' Q s)) =
        frontier (S.chart '' closedBall 0 (S.radial t)) := by
      rw [hPhiFrontier, hfront, S.frontier_chart_closedBall ht,
        S.image_sphere_eq_collar_level ht]
      ext y
      constructor
      · rintro ⟨x, ⟨⟨q, u⟩, ⟨_, hu⟩, hqx⟩, rfl⟩
        have hus : u = s := hu
        subst u
        refine ⟨q, mem_univ _, ?_⟩
        exact congrArg Phi2
          (Subtype.ext ((hef (q, s) (hes.symm ▸ ⟨mem_univ _, hs⟩)).trans hqx))
      · rintro ⟨q, _, rfl⟩
        refine ⟨e (q, s), ?_, rfl⟩
        exact ⟨(q, s), ⟨mem_univ _, rfl⟩,
          (hef (q, s) (hes.symm ▸ ⟨mem_univ _, hs⟩)).symm⟩
    exact IsCompact.eq_of_frontier_eq_of_preconnected_interior_compl
      (NormedSpace.unbounded_univ ℝ E3) hP (S.isCompact_chart_closedBall ht)
      hBi (S.isConnected_compl_chart_closedBall ht).isPreconnected hPi hfrontEq
  have hside : S.side = -1 := by
    rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
    · let q := (N.coordinate_inverse N.endCenter).1
      have ht0 : (1 / 2 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
      have ht1 : (3 / 4 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
      have hh0 := hheight (1 / 2) ht0
      have hh1 := hheight (3 / 4) ht1
      rw [hs, one_mul] at hh0 hh1
      let x := e (q, c + h * (1 / 2))
      have hxval : x.val = N.coordinate_map (q, c + h * (1 / 2)) :=
        hef _ (hes.symm ▸ ⟨mem_univ _, hh0⟩)
      have hxB : Phi2 x ∈ S.chart '' closedBall 0 (S.radial (3 / 4)) := by
        refine ⟨S.radial (1 / 2) • (S.boundary_map q).val, ?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
            mem_sphere_zero_iff_norm.mp (S.boundary_map q).property,
            mul_one, abs_of_pos (S.radial_pos _ ht0)]
          exact (S.radial_strictMono ht0 ht1 (by norm_num)).le
        · simpa only [hs, one_mul] using S.chart_collar q (1 / 2) ht0
      have heq := hballs (3 / 4) ht1
      rw [hs, one_mul] at heq
      obtain ⟨y, hy, hyx⟩ := heq.symm ▸ hxB
      have hyx' : y = x := Phi2.injective hyx
      have hxQ : x.val ∈ Q (c + h * (3 / 4)) := hyx' ▸ hy
      exfalso
      apply hxQ.2
      have hc := C1.end_neck_lower_cut_topology
        (show c + h * (3 / 4) ∈ Ioo (-L) L from ⟨hv.1.trans hh1.1, hh1.2⟩)
      change x.val ∈ interior (K (c + h * (3 / 4)))
      rw [hc.2.2.2.1]
      apply Or.inr
      rw [hxval]
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdom hh0⟩, ?_⟩
      rw [N.coordinate_inverse_map _ (hdom hh0)]
      exact ⟨hv.1.trans hh0.1, by linarith⟩
    · exact hs
  have himages (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      Phi2 '' ((Subtype.val : U2 → M) ⁻¹' Q (c - h * t)) =
          S.chart '' closedBall 0 (S.radial t) ∧
      Phi2 '' ((Subtype.val : U2 → M) ⁻¹' W (c - h * t)) =
          S.chart '' ball 0 (S.radial t) := by
    have hs := hheight t ht
    have hb := hballs t ht
    simp only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg] at hs hb
    refine ⟨hb, ?_⟩
    have hh := congrArg interior hb
    rw [hPhiInterior, (hcut hs).2.2.1, S.interior_chart_closedBall ht] at hh
    exact hh
  have htm : (3 / 4 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
  have htl : (1 / 2 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
  let rm := S.radial (3 / 4)
  let rl := S.radial (1 / 2)
  have hrm : 0 < rm := S.radial_pos _ htm
  have hrlt : rm < S.radius := S.radial_lt _ htm
  have hrlm : rl < rm := S.radial_strictMono htl htm (by norm_num)
  obtain ⟨D, hDs, _, hDf, hD, hDi⟩ := S.exists_chart_openPartialHomeomorph
  let Dm := D.restrOpen (ball 0 rm) isOpen_ball
  have hDmSub : ball (0 : E3) rm ⊆ D.source := by
    rw [hDs]
    exact ball_subset_ball hrlt.le
  have hDms : Dm.source = ball 0 rm := inter_eq_right.mpr hDmSub
  have hDmf : (Dm : E3 → E3) = S.chart := hDf
  have hDmt : Dm.target = S.chart '' ball 0 rm := by
    rw [← Dm.image_source_eq_target, hDms, hDmf]
  let incl := U2.openPartialHomeomorphSubtypeCoe hU2
  let G := (Dm.trans Phi2.symm.toHomeomorph.toOpenPartialHomeomorph).trans incl
  let J := G.symm
  have hJt : J.target = ball 0 rm := by
    change (Dm.source ∩ Dm ⁻¹' univ) ∩
      (fun z => Phi2.symm (Dm z)) ⁻¹' univ = ball 0 rm
    simp only [preimage_univ, inter_univ, hDms]
  have hJi : (J.symm : E3 → M) = fun z => (Phi2.symm (S.chart z)).val := by
    funext z
    change (Phi2.symm (Dm z)).val = (Phi2.symm (S.chart z)).val
    rw [hDmf]
  have hJs : J.source = W a := by
    have heq : J.symm '' J.target = W a := by
      rw [hJi, hJt]
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzW : Phi2 (Phi2.symm (S.chart z)) ∈
            Phi2 '' ((Subtype.val : U2 → M) ⁻¹' W a) := by
          rw [Phi2.apply_symm_apply, (himages (3 / 4) htm).2]
          exact ⟨z, hz, rfl⟩
        obtain ⟨y, hy, heq⟩ := hzW
        have hyx := congrArg (Subtype.val : U2 → M) (Phi2.injective heq)
        change (Phi2.symm (S.chart z)).val ∈ W a
        exact hyx ▸ (show y.val ∈ W a from hy)
      · intro hx
        have hxQ : x ∈ Q a := by
          obtain ⟨ho, hc, _, _, _, _⟩ := hcut (show a ∈ Ioo v L from ⟨hva, hab.trans hbL⟩)
          exact hc ▸ subset_closure hx
        let y : U2 := ⟨x, (hcut ⟨hva, hab.trans hbL⟩).2.2.2.2.1 hxQ⟩
        have hy : Phi2 y ∈ S.chart '' ball 0 rm :=
          (himages (3 / 4) htm).2 ▸ mem_image_of_mem Phi2 hx
        obtain ⟨z, hz, heq⟩ := hy
        refine ⟨z, hz, ?_⟩
        have hh := congrArg (fun w => (Phi2.symm w).val) heq
        simpa only [Phi2.symm_apply_apply] using hh
    exact J.symm.image_source_eq_target.symm.trans heq
  have hJf (x : U2) (hx : x.val ∈ J.source) : S.chart (J x.val) = Phi2 x := by
    have hi := J.left_inv hx
    rw [hJi] at hi
    have heq : Phi2.symm (S.chart (J x.val)) = x := Subtype.ext hi
    simpa only [Phi2.apply_symm_apply] using congrArg Phi2 heq
  have hincl : ContMDiffOn (𝓡 3) (𝓡 3) ∞ incl.symm C2.carrier := by
    have ht : incl.target = C2.carrier := U2.openPartialHomeomorphSubtypeCoe_target hU2
    have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ incl.symm) C2.carrier :=
      contMDiff_id.contMDiffOn.congr (fun x hx => incl.right_inv (ht.symm ▸ hx))
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U2 incl.symm C2.carrier x).mp (hc x hx)
  have hJsub : J.source ⊆ C2.carrier := by
    intro x hx
    rw [hJs] at hx
    obtain ⟨_, hc, _, _, hs, _⟩ := hcut (show a ∈ Ioo v L from ⟨hva, hab.trans hbL⟩)
    exact hs (hc ▸ subset_closure hx)
  have hJsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J J.source := by
    have hDmi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Dm.symm Dm.target :=
      hDi.contMDiffOn.mono (fun z hz => by
        obtain ⟨w, hw, rfl⟩ := Dm.image_source_eq_target.symm ▸ hz
        exact D.map_source hw.1)
    apply hDmi.comp (Phi2.contMDiff.comp_contMDiffOn (hincl.mono hJsub))
    intro x hx
    have hx' := J.map_source hx
    have hz := Dm.map_source (hDms.symm ▸ (hJt ▸ hx'))
    have heq : Dm (J x) = Phi2 (incl.symm x) := by
      rw [hDmf]
      have hv : (incl.symm x).val = x := incl.right_inv
        ((U2.openPartialHomeomorphSubtypeCoe_target hU2).symm ▸ hJsub hx)
      simpa only [hv] using hJf (incl.symm x) (hv.symm ▸ hx)
    change Phi2 (incl.symm x) ∈ Dm.target
    exact heq ▸ hz
  have hJismooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J.symm J.target := by
    rw [hJi, hJt]
    exact (contMDiff_subtype_val.comp Phi2.symm.contMDiff).comp_contMDiffOn
      (S.chart_smooth.mono (ball_subset_ball hrlt.le)).contMDiffOn
  obtain ⟨_, _, _, _, _, _, _, _, hcover, hover, _, _⟩ := hcuts a b hva hab hbL
  have hcover' : V b ∪ J.source = Y := by rw [hJs]; exact hcover
  have hover' : V b ∩ J.source = N.region a b := by rw [hJs]; exact hover
  have hannulus : J '' (N.region a b) = {z : E3 | rl < ‖z‖ ∧ ‖z‖ < rm} := by
    have hQb (x : U2) (hx : x.val ∈ J.source) :
        x.val ∈ Q b ↔ J x.val ∈ closedBall 0 rl := by
      constructor
      · intro hxb
        have him := (himages (1 / 2) htl).1 ▸ mem_image_of_mem Phi2 hxb
        obtain ⟨z, hz, heq⟩ := him
        have hzS : z ∈ ball (0 : E3) S.radius :=
          closedBall_subset_ball (hrlm.trans hrlt) hz
        have hxS : J x.val ∈ ball (0 : E3) S.radius :=
          ball_subset_ball hrlt.le (hJt ▸ J.map_source hx)
        have he := S.chart_injOn hxS hzS ((hJf x hx).trans heq.symm)
        exact he.symm ▸ hz
      · intro hxr
        have him : Phi2 x ∈ S.chart '' closedBall 0 rl :=
          ⟨J x.val, hxr, hJf x hx⟩
        obtain ⟨y, hy, heq⟩ := (himages (1 / 2) htl).1.symm ▸ him
        exact Phi2.injective heq ▸ hy
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxVJ := hover'.symm ▸ hx
      let y : U2 := ⟨x, hJsub hxVJ.2⟩
      have hout : J x ∉ closedBall (0 : E3) rl := by
        intro hh
        exact ((hQb y hxVJ.2).mpr hh).2 hxVJ.1
      exact ⟨lt_of_not_ge (fun hn => hout (mem_closedBall_zero_iff.mpr hn)),
        mem_ball_zero_iff.mp (hJt ▸ J.map_source hxVJ.2)⟩
    · intro hz
      have hzJ : z ∈ J.target := hJt.symm ▸ mem_ball_zero_iff.mpr hz.2
      have hxJ := J.map_target hzJ
      let x : U2 := ⟨J.symm z, hJsub hxJ⟩
      have hxQ : x.val ∉ Q b := by
        intro hx
        have hnorm := (hQb x hxJ).mp hx
        rw [J.right_inv hzJ] at hnorm
        exact (not_le_of_gt hz.1) (mem_closedBall_zero_iff.mp hnorm)
      have hxY : x.val ∈ Y := (hJs ▸ hxJ).1
      have hxV : x.val ∈ V b := by
        by_contra hnot
        exact hxQ ⟨hxY, hnot⟩
      exact ⟨x.val, hover' ▸ ⟨hxV, hxJ⟩, J.right_inv hzJ⟩
  refine ⟨Phi2, e, S, J, hes, het, hef, hei, he, heinv, hpsi, hside,
    himages, hJs, hJt, hJsmooth, hJismooth, hJi, hJf, hcover', hover', hannulus, ?_, ?_⟩
  · intro q t ht
    have ht1 : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨ht.1, ht.2.trans (by norm_num)⟩
    have hr : S.radial t • (S.boundary_map q).val ∈ J.target := by
      rw [hJt, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp (S.boundary_map q).property,
        mul_one, abs_of_pos (S.radial_pos t ht1)]
      exact S.radial_strictMono ht1 htm ht.2
    have hi : J.symm (S.radial t • (S.boundary_map q).val) =
        N.coordinate_map (q, c - h * t) := by
      rw [hJi]
      dsimp only
      rw [S.chart_collar q t ht1, Phi2.symm_apply_apply]
      have hh := hef (q, c + h * (S.side * t))
        (hes.symm ▸ ⟨mem_univ _, hheight t ht1⟩)
      simpa only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg] using hh
    refine ⟨hi ▸ J.map_target hr, ?_⟩
    rw [← hi, J.right_inv hr]
  · intro q t ht
    have ht1 : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hJi]
    dsimp only
    rw [S.chart_collar q t ht1, Phi2.symm_apply_apply]
    have hh := hef (q, c + h * (S.side * t))
      (hes.symm ▸ ⟨mem_univ _, hheight t ht1⟩)
    simpa only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg] using hh

end PoincareConjecture.M25.Topology3D
