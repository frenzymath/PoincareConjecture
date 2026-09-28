import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoCapCuts
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCompactPreimage
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.AntipodalBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.AntipodalPunctureExpansion
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapCoordinates










set_option autoImplicit false

open Set Metric IsManifold
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 2000000 in



theorem capCertificates_exists_projective_compact_side_dichotomy
    (hS : SchoenfliesService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (P : PoincareConjecture.StandardPuncturedProjectiveCover
      M C2.puncture C2.carrier)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    let L := C1.epsilon⁻¹
    let N := C1
    let Y := C1.carrier ∪ C2.carrier
    let K : ℝ → Set M := fun s => C1.carrier \ N.region s L
    let V : ℝ → Set M := fun s => interior (K s)
    let W : ℝ → Set M := fun s => Y \ K s
    let Q : ℝ → Set M := fun s => Y \ V s
    let Sigma : ℝ → Set M :=
      fun s => N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ))
    let D2 := projectiveCoverDomain C2.puncture
    ∃ v ∈ Ioo (-L) L,
      (Y \ C2.carrier) ⊆ V v ∧
      (∀ a b : ℝ, v < a → a < b → b < L →
        IsOpen (V b) ∧ IsOpen (W a) ∧
        closure (W a) = Q a ∧ interior (Q a) = W a ∧
        IsCompact (Q a) ∧ Q a ⊆ C2.carrier ∧
        frontier (W a) = Sigma a ∧ frontier (V b) = Sigma b ∧
        V b ∪ W a = Y ∧ V b ∩ W a = N.region a b ∧
        N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) ∧
        N.coordinate_map '' (univ ×ˢ Icc a b) ⊆ C2.carrier) ∧
      let +nondep c := (v + L) / 2
      let +nondep h := (L - v) / 4
      let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 1
      let kappa : RoundCylinderSpace → M :=
        fun z => N.coordinate_map (z.1, c + h * z.2)
      0 < h ∧ v < c - h ∧ c + h < L ∧
      ∃ F : RoundCylinderSpace → UnitThreeSphere,
        MapsTo F Omega D2 ∧ EqOn (P.cover ∘ F) kappa Omega ∧
        IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ F Omega ∧
        InjOn F Omega ∧
        Disjoint (F '' Omega) ((fun z => -F z) '' Omega) ∧
        D2 ∩ P.cover ⁻¹' (kappa '' Omega) =
          F '' Omega ∪ (fun z => -F z) '' Omega ∧
        let +nondep q0 := (N.coordinate_inverse N.endCenter).1
        let +nondep pole := -F (q0, 0)
        let +nondep theta := threeSphereStereographic pole
        let +nondep psi := fun z : RoundCylinderSpace => theta (F z)
        IsCollarEmbedding psi ∧
        ∃ (S : SchoenfliesData psi (1 / 4))
          (e : OpenPartialHomeomorph E3 UnitThreeSphere),
          e.source = ball 0 (S.radial (7 / 8)) ∧
          e.target = (fun x : E3 => theta.symm (S.chart x)) ''
            ball 0 (S.radial (7 / 8)) ∧
          (e : E3 → UnitThreeSphere) =
            (fun x => theta.symm (S.chart x)) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
          Disjoint e.target ((fun x : UnitThreeSphere => -x) '' e.target) ∧
          (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 4) (7 / 8) →
            e (S.radial t • (S.boundary_map q).val) = F (q, S.side * t) ∧
            e.symm (F (q, S.side * t)) =
              S.radial t • (S.boundary_map q).val) ∧
          (∀ t ∈ Icc (1 / 4 : ℝ) (7 / 8),
            let D := e '' closedBall 0 (S.radial t)
            IsCompact D ∧ IsConnected D ∧
            interior D = e '' ball 0 (S.radial t) ∧
            frontier D = F '' (univ ×ˢ ({S.side * t} : Set ℝ)) ∧
            Disjoint D ((fun x : UnitThreeSphere => -x) '' D)) ∧
          let s : ℝ → ℝ := fun t => c + h * (S.side * t)
          let D : ℝ → Set UnitThreeSphere :=
            fun t => e '' closedBall 0 (S.radial t)
          let Qt : ℝ → Set UnitThreeSphere :=
            fun t => D2 ∩ P.cover ⁻¹' Q (s t)
          let Wt : ℝ → Set UnitThreeSphere :=
            fun t => D2 ∩ P.cover ⁻¹' W (s t)
          (∀ t ∈ Icc (1 / 2 : ℝ) (13 / 16),
            s t ∈ Ioo v L ∧ IsCompact (Qt t) ∧
            interior (Qt t) = Wt t ∧
            frontier (Qt t) = frontier (D t) ∪
              (fun x : UnitThreeSphere => -x) '' frontier (D t) ∧
            (fun x : UnitThreeSphere => -x) '' Qt t = Qt t) ∧
          ((S.side = -1 ∧
            ∀ t ∈ Icc (1 / 2 : ℝ) (13 / 16),
              Qt t = D t ∪ (fun x : UnitThreeSphere => -x) '' D t ∧
              Wt t = interior (D t) ∪
                (fun x : UnitThreeSphere => -x) '' interior (D t)) ∨
           (S.side = 1 ∧
            ∀ t ∈ Icc (1 / 2 : ℝ) (13 / 16),
              Qt t = (interior (D t) ∪
                (fun x : UnitThreeSphere => -x) '' interior (D t))ᶜ ∧
              Wt t = (D t ∪ (fun x : UnitThreeSphere => -x) '' D t)ᶜ)) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := C1.epsilon⁻¹
  let N := C1
  let Y := C1.carrier ∪ C2.carrier
  let K (s : ℝ) := C1.carrier \ N.region s L
  let V (s : ℝ) := interior (K s)
  let W (s : ℝ) := Y \ K s
  let Q (s : ℝ) := Y \ V s
  let Sigma (s : ℝ) := N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ))
  let D2 := projectiveCoverDomain C2.puncture
  obtain ⟨v, hv, hbuffer, hcuts⟩ :=
    capCertificates_exists_buffered_cut_cover C1 C2 hcompact
  refine ⟨v, hv, hbuffer, hcuts, ?_⟩
  let c := (v + L) / 2
  let h := (L - v) / 4
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 1
  let kappa (z : RoundCylinderSpace) := N.coordinate_map (z.1, c + h * z.2)
  have hh : 0 < h := by dsimp [h, L]; linarith [hv.2]
  have hcminus : v < c - h := by dsimp [c, h]; linarith [hv.2]
  have hcplus : c + h < L := by dsimp [c, h]; linarith [hv.2]
  have hband {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
      c + h * s ∈ Icc (c - h) (c + h) := by
    have hlo := mul_le_mul_of_nonneg_left hs.1 hh.le
    have hhi := mul_le_mul_of_nonneg_left hs.2 hh.le
    constructor <;> linarith
  have hdom (z : RoundCylinderSpace) (hz : z ∈ Omega) :
      (z.1, c + h * z.2) ∈ N.cylinderDomain := by
    have hb := hband ⟨hz.2.1.le, hz.2.2.le⟩
    refine ⟨mem_univ _, ?_⟩
    exact ⟨hv.1.trans (hcminus.trans_le hb.1), hb.2.trans_lt hcplus⟩
  have hslab : N.coordinate_map '' (univ ×ˢ Icc (c - h) (c + h)) ⊆ C2.carrier :=
    (hcuts (c - h) (c + h) hcminus (by linarith) hcplus).2.2.2.2.2.2.2.2.2.2.2
  have hkU : MapsTo kappa Omega C2.carrier := by
    intro z hz
    exact hslab ⟨(z.1, c + h * z.2),
      ⟨mem_univ _, hband ⟨hz.2.1.le, hz.2.2.le⟩⟩, rfl⟩
  let height : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    { toFun := fun s => c + h * s
      invFun := fun s => (s - c) / h
      left_inv := by intro s; field_simp [hh.ne']; ring
      right_inv := by intro s; field_simp [hh.ne']; ring
      contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
      contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const h).contMDiff }
  let A := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr height
  have hNsource : N.end_chart.source = N.cylinderDomain := N.end_chart_source
  let n : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace M ∞ :=
    { toPartialEquiv := N.end_chart.toPartialEquiv
      open_source := N.end_chart.open_source
      open_target := N.end_chart.open_target
      contMDiffOn_toFun := N.end_chart_smooth
      contMDiffOn_invFun := N.end_chart_inverse_smooth }
  have hnloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      N.coordinate_map N.cylinderDomain :=
    fun z => ⟨n, hNsource.symm ▸ z.2, fun _ _ => rfl⟩
  have hkloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      kappa Omega := by
    intro z
    exact (A.isLocalDiffeomorph z.1).comp (𝓡 3) M (hnloc ⟨A z.1, hdom z.1 z.2⟩)
  have hkinj : InjOn kappa Omega := by
    intro z hz w hw heq
    exact A.injective (N.end_chart.injOn
      (hNsource.symm ▸ hdom z hz) (hNsource.symm ▸ hdom w hw) heq)
  let q0 := (N.coordinate_inverse N.endCenter).1
  have hzero : (q0, 0) ∈ Omega := ⟨mem_univ _, by norm_num, by norm_num⟩
  obtain ⟨x0, hx0, hx0map⟩ := P.image_eq.symm.subset (hkU hzero)
  obtain ⟨F, _hbase, hFD, hFc, hFloc, hFinj, _hnegD, _hnegc, _hnegloc, _hneginj,
    hFdis, hpreimage⟩ :=
    StandardPuncturedProjectiveCover.exists_based_projective_collar_lift P kappa
      (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num)
      hkloc hkinj hkU q0 x0 hx0 hx0map
  obtain ⟨hpsi, S, e, hes, het, hef, hed, heid, hedis, hray, hballs⟩ :=
    exists_antipodal_buffered_ball_chart_of_collar hS F hFloc hFinj hFdis q0
  refine ⟨hh, hcminus, hcplus, F, hFD, hFc, hFloc, hFinj, hFdis, hpreimage,
    hpsi, S, e, hes, het, hef, hed, heid, hedis, hray, hballs, ?_⟩
  let s (t : ℝ) := c + h * (S.side * t)
  let D (t : ℝ) := e '' closedBall 0 (S.radial t)
  let Qt (t : ℝ) := D2 ∩ P.cover ⁻¹' Q (s t)
  let Wt (t : ℝ) := D2 ∩ P.cover ⁻¹' W (s t)
  let negE : UnitThreeSphere ≃ₜ UnitThreeSphere :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := neg_neg
      right_inv := neg_neg
      continuous_toFun := continuous_neg
      continuous_invFun := continuous_neg }
  have hnegmem (Z : Set UnitThreeSphere) (x : UnitThreeSphere) :
      x ∈ negE '' Z ↔ -x ∈ Z := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      change -y = x at hxy
      simpa only [← hxy, neg_neg] using hy
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  have htall {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      t ∈ Ico (1 / 4 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hsigned {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      S.side * t ∈ Ioo (-1 : ℝ) 1 := by
    rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
    · rw [hs, one_mul]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [hs, neg_one_mul]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsrange {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      s t ∈ Ioo v L := by
    have hb := hband ⟨(hsigned ht).1.le, (hsigned ht).2.le⟩
    exact ⟨hcminus.trans_le hb.1, hb.2.trans_lt hcplus⟩
  have hslice {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
      D2 ∩ P.cover ⁻¹' Sigma (c + h * u) =
        F '' (univ ×ˢ ({u} : Set ℝ)) ∪
          negE '' (F '' (univ ×ˢ ({u} : Set ℝ))) := by
    ext x
    constructor
    · rintro ⟨hxD, z, hz, hzx⟩
      rcases z with ⟨q, r⟩
      have hr : r = c + h * u := hz.2
      subst r
      have hzO : (q, u) ∈ Omega := ⟨mem_univ _, hu⟩
      have hc : P.cover x = P.cover (F (q, u)) := hzx.symm.trans (hFc hzO).symm
      rcases (P.fibers x (F (q, u)) hxD (hFD hzO)).mp hc with hq | hq
      · exact Or.inl ⟨(q, u), ⟨mem_univ _, rfl⟩, hq.symm⟩
      · exact Or.inr ⟨F (q, u), ⟨(q, u), ⟨mem_univ _, rfl⟩, rfl⟩, hq.symm⟩
    · rintro (⟨⟨q, r⟩, ⟨_, hr⟩, rfl⟩ | ⟨y, ⟨⟨q, r⟩, ⟨_, hr⟩, rfl⟩, rfl⟩)
      · have hr' : r = u := hr
        subst r
        have hzO : (q, u) ∈ Omega := ⟨mem_univ _, hu⟩
        exact ⟨hFD hzO, (q, c + h * u), ⟨mem_univ _, rfl⟩, (hFc hzO).symm⟩
      · have hr' : r = u := hr
        subst r
        have hzO : (q, u) ∈ Omega := ⟨mem_univ _, hu⟩
        refine ⟨(neg_mem_projectiveCoverDomain_iff _ _).mpr (hFD hzO), ?_⟩
        change P.cover (-F (q, u)) ∈ Sigma (c + h * u)
        rw [StandardPuncturedProjectiveCover.cover_neg P (hFD hzO)]
        exact ⟨(q, c + h * u), ⟨mem_univ _, rfl⟩, (hFc hzO).symm⟩
  have htop (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (13 / 16)) :
      s t ∈ Ioo v L ∧ IsCompact (Qt t) ∧
        interior (Qt t) = Wt t ∧
        frontier (Qt t) = frontier (D t) ∪ negE '' frontier (D t) ∧
        negE '' Qt t = Qt t := by
    have ht' : t ∈ Icc (1 / 4 : ℝ) (7 / 8) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hs := hsrange ht'
    obtain ⟨_, hWo, hWcl, hQi, hQc, hQC2, hWf, _⟩ :=
      hcuts (s t) ((s t + L) / 2) hs.1 (by linarith [hs.2]) (by linarith [hs.2])
    have hQf : frontier (Q (s t)) = Sigma (s t) := by
      rw [hQc.isClosed.frontier_eq, hQi]
      rw [hWo.frontier_eq, hWcl] at hWf
      exact hWf
    obtain ⟨hcompactQt, hiQt, hfQt, hnQt⟩ :=
      StandardPuncturedProjectiveCover.compact_preimage_topology P hQc hQC2
    refine ⟨hs, hcompactQt, ?_, ?_, hnQt⟩
    · simpa only [hQi] using hiQt
    · rw [hQf] at hfQt
      rw [hfQt, hslice (hsigned ht'), (hballs t ht').2.2.2.1]
  have hQtpoint (t u : ℝ) (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8))
      (hu : u ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      F (q0, S.side * u) ∈ Qt t ↔ s t ≤ s u := by
    have huO : (q0, S.side * u) ∈ Omega := ⟨mem_univ _, hsigned hu⟩
    have hyN : N.coordinate_map (q0, s u) ∈ N.end_chart.target :=
      N.coordinate_map_mem (hdom _ huO)
    have hheight : (N.coordinate_inverse (N.coordinate_map (q0, s u))).2 = s u := by
      rw [N.coordinate_inverse_map _ (hdom _ huO).2]
    have hs := hsrange ht
    obtain ⟨_, _, _, hVi, _⟩ :=
      C1.end_neck_lower_cut_topology ⟨hv.1.trans hs.1, hs.2⟩
    have hVpoint : N.coordinate_map (q0, s u) ∈ V (s t) ↔ s u < s t := by
      change N.coordinate_map (q0, s u) ∈
        interior (C1.carrier \ C1.region (s t) C1.epsilon⁻¹) ↔ s u < s t
      rw [hVi]
      constructor
      · rintro (hx | hx)
        · rw [C1.closed_core_eq_complement_end] at hx
          exact False.elim (hx.2 hyN)
        · have hlt : (N.coordinate_inverse (N.coordinate_map (q0, s u))).2 < s t :=
            hx.2.2
          rwa [hheight] at hlt
      · intro hlt
        refine Or.inr ⟨hyN, ?_, ?_⟩
        · rw [hheight]
          exact hv.1.trans (hsrange hu).1
        · rwa [hheight]
    constructor
    · intro hx
      have hnot : N.coordinate_map (q0, s u) ∉ V (s t) := by
        simpa only [show P.cover (F (q0, S.side * u)) =
          N.coordinate_map (q0, s u) from hFc huO] using hx.2.2
      exact le_of_not_gt (fun hlt => hnot (hVpoint.mpr hlt))
    · intro hle
      refine ⟨hFD huO, ?_⟩
      change P.cover (F (q0, S.side * u)) ∈ Y \ V (s t)
      rw [show P.cover (F (q0, S.side * u)) =
        N.coordinate_map (q0, s u) from hFc huO]
      exact ⟨Or.inl (C1.end_chart_target_subset hyN),
        fun hx => (not_lt_of_ge hle) (hVpoint.mp hx)⟩
  have hcases (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (13 / 16)) :
      (S.side = -1 →
        Qt t = D t ∪ negE '' D t ∧
          Wt t = interior (D t) ∪ negE '' interior (D t)) ∧
      (S.side = 1 →
        Qt t = (interior (D t) ∪ negE '' interior (D t))ᶜ ∧
          Wt t = (D t ∪ negE '' D t)ᶜ) := by
    have ht' : t ∈ Icc (1 / 4 : ℝ) (7 / 8) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have houter : (7 / 8 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
    have hrpos : 0 < S.radial t := S.radial_pos t (htall ht')
    have hrR : S.radial t < S.radial (7 / 8) :=
      S.radial_strictMono (htall ht') houter (by linarith [ht.2])
    obtain ⟨hDc, _hDconn, hDi, _hDf, hDdis⟩ := hballs t ht'
    obtain ⟨_hst, hQc, hQi, hQf, hQneg⟩ := htop t ht
    have hDc' : IsClosed (D t) := hDc.isClosed
    have hQc' : IsClosed (Qt t) := hQc.isClosed
    let A := interior (D t)
    let E := (D t ∪ negE '' D t)ᶜ
    have hAconn : IsConnected A := by
      rw [show A = e '' ball 0 (S.radial t) from hDi]
      apply (isConnected_ball hrpos).image _ (e.continuousOn.mono ?_)
      rw [hes]
      exact ball_subset_ball hrR.le
    obtain ⟨_rho, Hext, _, _, _, _, _, _, _, _, hExttarget, _, _, hExtconn, _⟩ :=
      exists_antipodal_ball_exterior_chart e hrpos hrR hes hed heid hedis
    have hEconn : IsConnected E := by
      change IsConnected ((e '' closedBall 0 (S.radial t) ∪
        (fun x : UnitThreeSphere => -x) '' (e '' closedBall 0 (S.radial t)))ᶜ)
      rwa [hExttarget] at hExtconn
    have hDtarget : D t ⊆ e.target := e.image_closedBall_subset_target hes hrR
    have hAavoid : Disjoint A (frontier (Qt t)) := by
      apply disjoint_left.mpr
      intro x hx hxf
      rw [hQf] at hxf
      rcases hxf with hxD | ⟨y, hy, hyx⟩
      · exact disjoint_left.mp disjoint_interior_frontier hx hxD
      · exact disjoint_left.mp hDdis (interior_subset hx)
          ⟨y, hDc'.frontier_subset hy, hyx⟩
    have hEavoid : Disjoint E (frontier (Qt t)) := by
      apply disjoint_left.mpr
      intro x hx hxf
      rw [hQf] at hxf
      rcases hxf with hxD | ⟨y, hy, hyx⟩
      · exact hx (Or.inl (hDc'.frontier_subset hxD))
      · exact hx (Or.inr ⟨y, hDc'.frontier_subset hy, hyx⟩)
    have label {Z : Set UnitThreeSphere} (hZ : IsPreconnected Z)
        (havoid : Disjoint Z (frontier (Qt t))) :
        Z ⊆ interior (Qt t) ∨ Z ⊆ (Qt t)ᶜ := by
      apply hZ.subset_or_subset isOpen_interior hQc'.isOpen_compl
      · exact disjoint_left.mpr (fun _ hx hi => hi (interior_subset hx))
      · intro x hx
        by_cases hxQ : x ∈ Qt t
        · apply Or.inl
          exact (mem_interior_iff_notMem_frontier hxQ).mpr
            (fun hxf => disjoint_left.mp havoid hx hxf)
        · exact Or.inr hxQ
    let um := (t + 1 / 4) / 2
    let up := (t + 7 / 8) / 2
    have hum : um ∈ Icc (1 / 4 : ℝ) (7 / 8) := by
      dsimp [um]; constructor <;> linarith [ht.1, ht.2]
    have hup : up ∈ Icc (1 / 4 : ℝ) (7 / 8) := by
      dsimp [up]; constructor <;> linarith [ht.1, ht.2]
    have humt : um < t := by dsimp [um]; linarith [ht.1]
    have htup : t < up := by dsimp [up]; linarith [ht.2]
    have hupouter : up < 7 / 8 := by dsimp [up]; linarith [ht.2]
    let xm := F (q0, S.side * um)
    let xp := F (q0, S.side * up)
    let vec (u : ℝ) := S.radial u • (S.boundary_map q0).val
    have hnorm {u : ℝ} (hu : u ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
        ‖vec u‖ = S.radial u := by
      dsimp only [vec]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (S.radial_pos u (htall hu)),
        mem_sphere_zero_iff_norm.mp (S.boundary_map q0).property, mul_one]
    have hxm : xm ∈ A := by
      rw [show A = e '' ball 0 (S.radial t) from hDi]
      refine ⟨vec um, ?_, (hray q0 um hum).1⟩
      rw [mem_ball_zero_iff, hnorm hum]
      exact S.radial_strictMono (htall hum) (htall ht') humt
    have hxpAnn : xp ∈ (D t)ᶜ ∩ e.target := by
      rw [e.compl_image_closedBall_inter_target hes hrR]
      refine ⟨vec up, ?_, (hray q0 up hup).1⟩
      change S.radial t < ‖vec up‖ ∧ ‖vec up‖ < S.radial (7 / 8)
      rw [hnorm hup]
      exact ⟨S.radial_strictMono (htall ht') (htall hup) htup,
        S.radial_strictMono (htall hup) houter hupouter⟩
    have hxp : xp ∈ E := by
      rintro (hx | ⟨y, hy, hyx⟩)
      · exact hxpAnn.1 hx
      · exact disjoint_left.mp hedis hxpAnn.2 ⟨y, hDtarget hy, hyx⟩
    have hnegQt {x : UnitThreeSphere} (hx : x ∈ Qt t) : -x ∈ Qt t := by
      rw [← hQneg]
      exact ⟨x, hx, rfl⟩
    have hnegInt {x : UnitThreeSphere} (hx : x ∈ interior (Qt t)) :
        -x ∈ interior (Qt t) := by
      have heq : negE '' interior (Qt t) = interior (Qt t) := by
        rw [negE.image_interior, hQneg]
      rw [← heq]
      exact ⟨x, hx, rfl⟩
    have hfrontQ : frontier (D t) ⊆ Qt t :=
      fun _ hx => hQc'.frontier_subset (hQf.symm ▸ Or.inl hx)
    have hfrontNotInt {x : UnitThreeSphere} (hx : x ∈ frontier (D t)) :
        x ∉ interior (Qt t) :=
      fun hi => disjoint_left.mp disjoint_interior_frontier hi (hQf.symm ▸ Or.inl hx)
    have hDsplit {x : UnitThreeSphere} (hx : x ∈ D t) :
        x ∈ A ∨ x ∈ frontier (D t) := by
      by_cases hi : x ∈ A
      · exact Or.inl hi
      · exact Or.inr ((mem_frontier_iff_notMem_interior hx).mpr hi)
    constructor
    · intro hside
      have hxmQ : xm ∈ Qt t := by
        apply (hQtpoint t um ht' hum).mpr
        dsimp only [s]
        rw [hside, neg_one_mul, neg_one_mul]
        nlinarith
      have hxpQ : xp ∉ Qt t := by
        intro hx
        have hle := (hQtpoint t up ht' hup).mp hx
        dsimp only [s] at hle
        rw [hside, neg_one_mul, neg_one_mul] at hle
        nlinarith
      have hAQ : A ⊆ interior (Qt t) :=
        (label hAconn.isPreconnected hAavoid).resolve_right
          (fun hnot => hnot hxm hxmQ)
      have hEnot : E ⊆ (Qt t)ᶜ :=
        (label hEconn.isPreconnected hEavoid).resolve_left
          (fun hyes => hxpQ (interior_subset (hyes hxp)))
      have hDQ : D t ⊆ Qt t := by
        intro x hx
        exact (hDsplit hx).elim (fun hi => interior_subset (hAQ hi)) (fun hf => hfrontQ hf)
      have hclosedEq : Qt t = D t ∪ negE '' D t := by
        apply Subset.antisymm
        · intro x hx
          by_contra hn
          exact hEnot hn hx
        · rintro x (hx | ⟨y, hy, rfl⟩)
          · exact hDQ hx
          · exact hnegQt (hDQ hy)
      have hopenEq : interior (Qt t) = A ∪ negE '' A := by
        apply Subset.antisymm
        · intro x hx
          have hclosed := hclosedEq ▸ interior_subset hx
          rcases hclosed with hxD | ⟨y, hy, rfl⟩
          · rcases hDsplit hxD with hi | hf
            · exact Or.inl hi
            · exact False.elim (hfrontNotInt hf hx)
          · rcases hDsplit hy with hi | hf
            · exact Or.inr ⟨y, hi, rfl⟩
            · have hyi : y ∈ interior (Qt t) := by
                simpa only [neg_neg] using
                  (hnegInt hx : -(-y) ∈ interior (Qt t))
              exact False.elim (hfrontNotInt hf hyi)
        · rintro x (hx | ⟨y, hy, rfl⟩)
          · exact hAQ hx
          · exact hnegInt (hAQ hy)
      exact ⟨hclosedEq, hQi ▸ hopenEq⟩
    · intro hside
      have hxmQ : xm ∉ Qt t := by
        intro hx
        have hle := (hQtpoint t um ht' hum).mp hx
        dsimp only [s] at hle
        rw [hside, one_mul, one_mul] at hle
        nlinarith
      have hxpQ : xp ∈ Qt t := by
        apply (hQtpoint t up ht' hup).mpr
        dsimp only [s]
        rw [hside, one_mul, one_mul]
        nlinarith
      have hAnot : A ⊆ (Qt t)ᶜ :=
        (label hAconn.isPreconnected hAavoid).resolve_left
          (fun hyes => hxmQ (interior_subset (hyes hxm)))
      have hEQ : E ⊆ interior (Qt t) :=
        (label hEconn.isPreconnected hEavoid).resolve_right
          (fun hnot => hnot hxp hxpQ)
      have hantiNot : negE '' A ⊆ (Qt t)ᶜ := by
        rintro x ⟨y, hy, rfl⟩ hx
        have hyQ : y ∈ Qt t := by
          simpa only [neg_neg] using (hnegQt hx : -(-y) ∈ Qt t)
        exact hAnot hy hyQ
      have hclosedEq : Qt t = (A ∪ negE '' A)ᶜ := by
        apply Subset.antisymm
        · intro x hx
          rintro (hi | hi)
          · exact hAnot hi hx
          · exact hantiNot hi hx
        · intro x hx
          by_cases hxD : x ∈ D t ∪ negE '' D t
          · rcases hxD with hxD | ⟨y, hy, rfl⟩
            · exact (hDsplit hxD).elim
                (fun hi => False.elim (hx (Or.inl hi))) (fun hf => hfrontQ hf)
            · apply hnegQt
              rcases hDsplit hy with hi | hf
              · exact False.elim (hx (Or.inr ⟨y, hi, rfl⟩))
              · exact hfrontQ hf
          · exact interior_subset (hEQ hxD)
      have hopenEq : interior (Qt t) = E := by
        apply Subset.antisymm
        · intro x hx
          rintro (hxD | ⟨y, hy, rfl⟩)
          · rcases hDsplit hxD with hi | hf
            · exact hAnot hi (interior_subset hx)
            · exact hfrontNotInt hf hx
          · have hyi : y ∈ interior (Qt t) := by
              simpa only [neg_neg] using
                  (hnegInt hx : -(-y) ∈ interior (Qt t))
            rcases hDsplit hy with hi | hf
            · exact hAnot hi (interior_subset hyi)
            · exact hfrontNotInt hf hyi
        · exact hEQ
      exact ⟨hclosedEq, hQi ▸ hopenEq⟩
  refine ⟨htop, ?_⟩
  rcases mul_self_eq_one_iff.mp S.side_sq with hside | hside
  · exact Or.inr ⟨hside, fun t ht => (hcases t ht).2 hside⟩
  · exact Or.inl ⟨hside, fun t ht => (hcases t ht).1 hside⟩

end PoincareConjecture.M25.Topology3D
