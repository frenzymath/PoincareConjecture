import PoincareConjecture.Proofs.M03.RicciPairRegularity
import PoincareConjecture.Proofs.M03.ScalarMixedDerivative

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem connection_rate_ricci_pair_smooth
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (F.connection t).ricci y (Y y) (Z y)) x := by
  let c := extChartAt (𝓡 n) x
  have hcx : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hcxt : c x ∈ c.target := mem_extChartAt_target x
  have hc : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm (c x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hcxt)
  have hn : interior J ×ˢ (c.target ∩ c.symm ⁻¹' U) ∈ 𝓝 (t, c x) :=
    prod_mem_nhds (isOpen_interior.mem_nhds ht)
      (Filter.inter_mem (extChartAt_target_mem_nhds' hcxt)
        (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa only [hcx] using hx))))
  have hh := (contDiffOn_ricciFlow_ricci_chart_pair F hU Y Z hY hZ x).contDiffAt hn
  have hs := hh.comp (c x) (contDiffAt_const.prodMk contDiffAt_id)
  rw [contMDiffAt_iff_source]
  rw [(𝓡 n).range_eq_univ, contMDiffWithinAt_univ]
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
    ((fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.connection p.1).ricci (c.symm p.2)
        (Y (c.symm p.2)) (Z (c.symm p.2))) ∘ fun z => (t, z)) (c x)
  exact hs.contMDiffAt

section EndpointGluing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators
open Bundle Manifold Filter



theorem exists_ricciFlow_gluing_of_uniform_metric_jets
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (F : RicciFlow n M (Ico 0 T))
    (G : RicciFlow n M (Ico T (T + δ)))
    (hjets : ∀ x0 : M,
      let V := EuclideanSpace ℝ (Fin n)
      let c := chartAt V x0
      let e := trivializationAt V (TangentSpace (𝓡 n)) x0
      let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      let f := fun (s : ℝ) (i j : Fin n) (z : V) =>
        (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
      let g := fun (i j : Fin n) (z : V) =>
        (G.metric T).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
      ∀ q : ℕ, ∀ K : Set V, IsCompact K → K ⊆ c.target →
        ∀ i j : Fin n,
          TendstoUniformlyOn (fun s z => iteratedFDeriv ℝ q (f s i j) z)
            (iteratedFDeriv ℝ q (g i j)) (𝓝[<] T) K) :
    ∃ H : RicciFlow n M (Ico 0 (T + δ)),
      EqOn F.metric H.metric (Ico 0 T) ∧
      EqOn G.metric H.metric (Ico T (T + δ)) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let data : ℝ → Σ h : RiemannianMetric n M, LeviCivitaData h :=
    fun t => if t < T then ⟨F.metric t, F.connection t⟩ else ⟨G.metric t, G.connection t⟩
  let g : ℝ → RiemannianMetric n M := fun t => (data t).1
  let D : (t : ℝ) → LeviCivitaData (g t) := fun t => (data t).2
  have hgl (t : ℝ) (ht : t < T) : g t = F.metric t := by simp only [g, data, if_pos ht]
  have hgr (t : ℝ) (ht : T ≤ t) : g t = G.metric t := by
    simp only [g, data, if_neg (not_lt.mpr ht)]
  have hDl (t : ℝ) (ht : t < T) (x : M) (v w : TangentSpace (𝓡 n) x) :
      (D t).ricci x v w = (F.connection t).ricci x v w := by
    exact congrArg (fun p : Σ h : RiemannianMetric n M, LeviCivitaData h =>
      p.2.ricci x v w)
      (show data t = ⟨F.metric t, F.connection t⟩ by simp only [data, if_pos ht])
  have hDr (t : ℝ) (ht : T ≤ t) (x : M) (v w : TangentSpace (𝓡 n) x) :
      (D t).ricci x v w = (G.connection t).ricci x v w := by
    exact congrArg (fun p : Σ h : RiemannianMetric n M, LeviCivitaData h =>
      p.2.ricci x v w)
      (show data t = ⟨G.metric t, G.connection t⟩ by simp only [data, if_neg (not_lt.mpr ht)])
  have hchart {J : Set ℝ} (a : ℝ → RiemannianMetric n M)
      (ha : RiemannianMetric.IsSmoothFamilyOn a J) (x0 : M) :
      let c := chartAt V x0
      let e := trivializationAt V (TangentSpace (𝓡 n)) x0
      let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      ∀ i j : Fin n, ContDiffOn ℝ ∞
        (fun p : ℝ × V => (a p.1).inner (c.symm p.2)
          (E i (c.symm p.2)) (E j (c.symm p.2))) (J ×ˢ c.target) := by
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    dsimp only
    intro i j
    have hE (k : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (E k)) e.baseSet := e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb k
    have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × V => (p.1, c.symm p.2)) (J ×ˢ c.target) :=
      contMDiffOn_fst.prodMk ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞)
        (x := x0)).comp contMDiffOn_snd (fun _ hp => hp.2))
    have hh := (contMDiffOn_family_metric_pair ha (E i) (E j) (hE i) (hE j)).comp hc
      (fun p hp => ⟨hp.1, by
        simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hp.2⟩)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiffOn
  have hmid (x0 : M) :
      let c := chartAt V x0
      let e := trivializationAt V (TangentSpace (𝓡 n)) x0
      let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      ∀ i j : Fin n, ContDiffOn ℝ ∞
        (fun p : ℝ × V => (g p.1).inner (c.symm p.2)
          (E i (c.symm p.2)) (E j (c.symm p.2)))
        (Ioo (T / 2) (T + δ) ×ˢ c.target) := by
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let a := fun (t : ℝ) (i : Fin n × Fin n) (z : V) =>
      (F.metric t).inner (c.symm z) (E i.1 (c.symm z)) (E i.2 (c.symm z))
    let b := fun (t : ℝ) (i : Fin n × Fin n) (z : V) =>
      (G.metric t).inner (c.symm z) (E i.1 (c.symm z)) (E i.2 (c.symm z))
    let f := fun (i : Fin n × Fin n) (t : ℝ) (z : V) =>
      (g t).inner (c.symm z) (E i.1 (c.symm z)) (E i.2 (c.symm z))
    let r := fun (i : Fin n × Fin n) (t : ℝ) (z : V) =>
      -2 * (D t).ricci (c.symm z) (E i.1 (c.symm z)) (E i.2 (c.symm z))
    have hfl (i : Fin n × Fin n) (t : ℝ) (ht : t < T) : f i t = a t i := by
      funext z
      dsimp only [f, a]
      rw [hgl t ht]
    have hfr (i : Fin n × Fin n) (t : ℝ) (ht : T ≤ t) : f i t = b t i := by
      funext z
      dsimp only [f, b]
      rw [hgr t ht]
    have hasm (i : Fin n × Fin n) : ContDiffOn ℝ ∞
        (fun p : ℝ × V => a p.1 i p.2) (Ico 0 T ×ˢ c.target) :=
      hchart F.metric F.smooth x0 i.1 i.2
    have hbsm (i : Fin n × Fin n) : ContDiffOn ℝ ∞
        (fun p : ℝ × V => b p.1 i p.2) (Ico T (T + δ) ×ˢ c.target) :=
      hchart G.metric G.smooth x0 i.1 i.2
    have haJ (i : Fin n × Fin n) (q : ℕ) :=
      contDiffOn_iteratedFDeriv_family_of_isOpen_spatial c.open_target
        (fun t => a t i) (hasm i) q
    have hbJ (i : Fin n × Fin n) (q : ℕ) :=
      contDiffOn_iteratedFDeriv_family_of_isOpen_spatial c.open_target
        (fun t => b t i) (hbsm i) q
    have hspatial (i : Fin n × Fin n) (t : ℝ) : ContDiffOn ℝ ∞ (f i t) c.target := by
      have hconst : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g t) univ :=
        ((g t).contMDiff.comp contMDiff_snd).contMDiffOn
      exact (hchart (fun _ : ℝ => g t) hconst x0 i.1 i.2).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨mem_univ (0 : ℝ), hz⟩)
    have hcontinuous (i : Fin n × Fin n) (q : ℕ) : ContinuousOn
        (fun p : ℝ × V => iteratedFDeriv ℝ q (f i p.1) p.2)
        (Ioo (T / 2) (T + δ) ×ˢ c.target) := by
      intro p hp
      by_cases hpt : p.1 = T
      · obtain ⟨t, z⟩ := p
        dsimp only at hpt hp
        subst t
        obtain ⟨K, hK, hzK, hKU⟩ := exists_compact_subset c.open_target hp.2
        have hleft : ContinuousWithinAt
            (fun p : ℝ × V => iteratedFDeriv ℝ q (f i p.1) p.2)
            (Ioo (T / 2) T ×ˢ c.target) (T, z) := by
          let l := 𝓝[Ioo (T / 2) T ×ˢ c.target] (T, z)
          have ht : Tendsto (fun p : ℝ × V => p.1) l (𝓝[<] T) := by
            apply tendsto_nhdsWithin_iff.mpr
            refine ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
            filter_upwards [self_mem_nhdsWithin] with p hp
            exact hp.1.2
          have hz : Tendsto (fun p : ℝ × V => p.2) l (𝓝[K] z) := by
            apply tendsto_nhdsWithin_iff.mpr
            have hh : Tendsto (fun p : ℝ × V => p.2) l (𝓝 z) :=
              continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            exact ⟨hh, hh (mem_interior_iff_mem_nhds.mp hzK)⟩
          have hu : TendstoUniformlyOn
              (fun p : ℝ × V => iteratedFDeriv ℝ q (a p.1 i))
              (iteratedFDeriv ℝ q (b T i)) l K := by
            intro u hu
            exact ht (hjets x0 q K hK hKU i.1 i.2 u hu)
          have hbcont : ContinuousAt (iteratedFDeriv ℝ q (b T i)) z := by
            have hh := (hbJ i q).continuousOn.comp
              (continuousOn_const.prodMk continuousOn_id)
              (fun y hy => ⟨⟨le_rfl, by linarith⟩, hy⟩)
            exact hh.continuousAt (c.open_target.mem_nhds hp.2)
          have hh := hu.tendsto_comp hbcont.continuousWithinAt hz
          change Tendsto (fun p : ℝ × V => iteratedFDeriv ℝ q (f i p.1) p.2)
            l (𝓝 (iteratedFDeriv ℝ q (f i T) z))
          rw [hfr i T le_rfl]
          apply hh.congr'
          filter_upwards [self_mem_nhdsWithin] with p hp
          rw [hfl i p.1 hp.1.2]
        have hright : ContinuousWithinAt
            (fun p : ℝ × V => iteratedFDeriv ℝ q (f i p.1) p.2)
            (Ico T (T + δ) ×ˢ c.target) (T, z) := by
          apply ((hbJ i q).continuousOn (T, z) ⟨⟨le_rfl, by linarith⟩, hp.2⟩).congr
          · intro p hp
            rw [hfr i p.1 hp.1.1]
          · rw [hfr i T le_rfl]
        apply (hleft.union hright).mono
        intro p hp
        by_cases h : p.1 < T
        · exact Or.inl ⟨⟨hp.1.1, h⟩, hp.2⟩
        · exact Or.inr ⟨⟨le_of_not_gt h, hp.1.2⟩, hp.2⟩
      · rcases lt_or_gt_of_ne hpt with hlt | hgt
        · have hn : Ico 0 T ×ˢ c.target ∈ 𝓝 p :=
            prod_mem_nhds (Ico_mem_nhds (by linarith [hp.1.1]) hlt)
              (c.open_target.mem_nhds hp.2)
          apply ((haJ i q).continuousOn.continuousAt hn).congr_of_eventuallyEq
              (show _ =ᶠ[𝓝 p] _ from ?_) |>.continuousWithinAt
          filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
            (isOpen_Iio.mem_nhds hlt)] with p hp
          rw [hfl i p.1 hp]
        · have hn : Ico T (T + δ) ×ˢ c.target ∈ 𝓝 p :=
            prod_mem_nhds (Ico_mem_nhds hgt hp.1.2) (c.open_target.mem_nhds hp.2)
          apply ((hbJ i q).continuousOn.continuousAt hn).congr_of_eventuallyEq
              (show _ =ᶠ[𝓝 p] _ from ?_) |>.continuousWithinAt
          filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
            (isOpen_Ioi.mem_nhds hgt)] with p hp
          rw [hfr i p.1 hp.le]
    have htime (i : Fin n × Fin n) (q : ℕ) (t : ℝ)
        (ht : t ∈ Ioo (T / 2) (T + δ)) (htT : t ≠ T)
        (z : V) (hz : z ∈ c.target) : HasDerivAt
          (fun s => iteratedFDeriv ℝ q (f i s) z)
          (iteratedFDeriv ℝ q (r i t) z) t := by
      rcases lt_or_gt_of_ne htT with hlt | hgt
      · have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × V => a p.1 i p.2)
            (Ioo 0 T ×ˢ c.target) :=
          (hasm i).mono (prod_mono Ioo_subset_Ico_self subset_rfl)
        have hd := hasDerivAt_iteratedFDeriv_family isOpen_Ioo c.open_target
          (fun s => a s i) hsm q ⟨by linarith [ht.1], hlt⟩ hz
        have hr : (fun y => deriv (fun s => a s i y) t) =ᶠ[𝓝 z] r i t := by
          filter_upwards [c.open_target.mem_nhds hz] with y hy
          have hh := (F.equation t ⟨by linarith [ht.1], hlt⟩
            (c.symm y) (E i.1 (c.symm y)) (E i.2 (c.symm y))).hasDerivAt
              (Ico_mem_nhds (by linarith [ht.1]) hlt)
          dsimp only [r]
          rw [hDl t hlt]
          exact hh.deriv
        rw [(hr.iteratedFDeriv (𝕜 := ℝ) q).eq_of_nhds] at hd
        apply hd.congr_of_eventuallyEq
        filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
        rw [hfl i s hs]
      · have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × V => b p.1 i p.2)
            (Ioo T (T + δ) ×ˢ c.target) :=
          (hbsm i).mono (prod_mono Ioo_subset_Ico_self subset_rfl)
        have hd := hasDerivAt_iteratedFDeriv_family isOpen_Ioo c.open_target
          (fun s => b s i) hsm q ⟨hgt, ht.2⟩ hz
        have hr : (fun y => deriv (fun s => b s i y) t) =ᶠ[𝓝 z] r i t := by
          filter_upwards [c.open_target.mem_nhds hz] with y hy
          have hh := (G.equation t ⟨hgt.le, ht.2⟩
            (c.symm y) (E i.1 (c.symm y)) (E i.2 (c.symm y))).hasDerivAt
              (Ico_mem_nhds hgt ht.2)
          dsimp only [r]
          rw [hDr t hgt.le]
          exact hh.deriv
        rw [(hr.iteratedFDeriv (𝕜 := ℝ) q).eq_of_nhds] at hd
        apply hd.congr_of_eventuallyEq
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
        rw [hfr i s hs.le]
    have hr (k : ℕ)
        (hf : ∀ i q, ContDiffOn ℝ k
          (fun p : ℝ × V => iteratedFDeriv ℝ q (f i p.1) p.2)
          (Ioo (T / 2) (T + δ) ×ˢ c.target)) :
        ∀ i q, ContDiffOn ℝ k
          (fun p : ℝ × V => iteratedFDeriv ℝ q (r i p.1) p.2)
          (Ioo (T / 2) (T + δ) ×ˢ c.target) := by
      have hRic := contDiffOn_ricci_coordinate_jets_of_metric_coordinate_jets
        g D isOpen_Ioo x0 k (fun q i j => hf (i, j) q)
      let L : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft
        (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 (-2 : ℝ) (by norm_num))
      intro i q
      have he (t : ℝ) : r i t = L ∘ (fun z =>
          (D t).ricci (c.symm z) (E i.1 (c.symm z)) (E i.2 (c.symm z))) := rfl
      have hh := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin q => V) ℝ ℝ) L.toContinuousLinearMap).contDiff.comp_contDiffOn
          (hRic q i.1 i.2)
      apply hh.congr
      intro p hp
      rw [he, L.iteratedFDeriv_comp_left]
      rfl
    have hh := contDiffOn_of_spatial_jet_evolution c.open_target
      (show T / 2 < T by linarith) (show T < T + δ by linarith) f r
      (fun i t _ => hspatial i t) hcontinuous htime hr
    exact fun i j => hh.2.1 (i, j)
  have hfull (x0 : M) :
      let c := chartAt V x0
      let e := trivializationAt V (TangentSpace (𝓡 n)) x0
      let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      ∀ i j : Fin n, ContDiffOn ℝ ∞
        (fun p : ℝ × V => (g p.1).inner (c.symm p.2)
          (E i (c.symm p.2)) (E j (c.symm p.2)))
        (Ico 0 (T + δ) ×ˢ c.target) := by
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    dsimp only
    intro i j p hp
    by_cases ht : p.1 < T
    · have hn : Ico 0 T ×ˢ c.target ∈ 𝓝[Ico 0 (T + δ) ×ˢ c.target] p := by
        have hnear : ∀ᶠ q : ℝ × V in 𝓝 p, q.1 < T :=
          (continuous_fst.tendsto p) (Iio_mem_nhds ht)
        filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with y hy hyt
        exact ⟨⟨hy.1.1, hyt⟩, hy.2⟩
      apply ((hchart F.metric F.smooth x0 i j p ⟨⟨hp.1.1, ht⟩, hp.2⟩).mono_of_mem_nhdsWithin
        hn).congr_of_eventuallyEq_of_mem _ hp
      filter_upwards [hn] with y hy
      rw [hgl y.1 hy.1.2]
    · by_cases he : p.1 = T
      · have hn : Ioo (T / 2) (T + δ) ×ˢ c.target ∈ 𝓝 p :=
          prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨by rw [he]; linarith, hp.1.2⟩)
            (c.open_target.mem_nhds hp.2)
        exact ((hmid x0 i j).contDiffAt hn).contDiffWithinAt
      · have hgt : T < p.1 := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he)
        have hn : Ico T (T + δ) ×ˢ c.target ∈ 𝓝[Ico 0 (T + δ) ×ˢ c.target] p := by
          have hnear : ∀ᶠ q : ℝ × V in 𝓝 p, T < q.1 :=
            (continuous_fst.tendsto p) (Ioi_mem_nhds hgt)
          filter_upwards [self_mem_nhdsWithin,
            Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with y hy hyt
          exact ⟨⟨hyt.le, hy.1.2⟩, hy.2⟩
        apply ((hchart G.metric G.smooth x0 i j p ⟨⟨hgt.le, hp.1.2⟩, hp.2⟩).mono_of_mem_nhdsWithin
          hn).congr_of_eventuallyEq_of_mem _ hp
        filter_upwards [hn] with y hy
        rw [hgr y.1 hy.1.1]
  have hsmooth : RiemannianMetric.IsSmoothFamilyOn g (Ico 0 (T + δ)) := by
    intro p hp
    let x0 := p.2
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let BC := fun q : ℝ × M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 q.2 x0 q.2 ((g q.1).inner q.2)
    let P : Fin n → Fin n → V →L[ℝ] V →L[ℝ] ℝ :=
      fun i j => (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)
    have hx0 : x0 ∈ e.baseSet := mem_baseSet_trivializationAt V (TangentSpace (𝓡 n)) x0
    have hEvalue {y : M} (hy : y ∈ e.baseSet) (i : Fin n) :
        E i y = e.symmL ℝ y (cb i) := by
      dsimp only [E]
      rw [e.localFrame_apply_of_mem_baseSet cb hy]
      simp only [Trivialization.basisAt, Module.Basis.map_apply,
        Trivialization.linearEquivAt_symm_apply]
      exact (Trivialization.symmL_apply (R := ℝ) e hy (cb i)).symm
    have hEexpand {y : M} (hy : y ∈ e.baseSet) (v : V) :
        e.symmL ℝ y v = ∑ i : Fin n, v i • E i y := by
      have hv : v = ∑ i : Fin n, v i • cb i := by
        simpa only [cb, EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis] using
          ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
      calc
        _ = e.symmL ℝ y (∑ i : Fin n, v i • cb i) := congrArg (e.symmL ℝ y) hv
        _ = _ := by simp only [map_sum, map_smul, hEvalue hy]
    have hBCeq (q : ℝ × M) (hy : q.2 ∈ e.baseSet) :
        BC q = ∑ i : Fin n, ∑ j : Fin n,
          (g q.1).inner q.2 (E i q.2) (E j q.2) • P i j := by
      ext v w
      dsimp only [BC]
      rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hy hy (by simp)]
      rw [← Trivialization.symmL_apply (R := ℝ) e hy v,
        ← Trivialization.symmL_apply (R := ℝ) e hy w]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_coe, id_eq]
      rw [hEexpand hy, hEexpand hy]
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, Finset.mul_sum, P]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change w j * (v i * (g q.1).inner q.2 (E i q.2) (E j q.2)) =
        (g q.1).inner q.2 (E i q.2) (E j q.2) * (v i * w j)
      ring
    have hscalar (i j : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => (g q.1).inner q.2 (E i q.2) (E j q.2))
        (Ico 0 (T + δ) ×ˢ e.baseSet) := by
      have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) ∞
          (fun q : ℝ × M => (q.1, c q.2)) (Ico 0 (T + δ) ×ˢ c.source) :=
        contMDiffOn_fst.prodMk ((contMDiffOn_chart (I := 𝓡 n) (n := ∞) (x := x0)).comp
          contMDiffOn_snd (fun _ hq => hq.2))
      have hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × V => (g q.1).inner (c.symm q.2)
            (E i (c.symm q.2)) (E j (c.symm q.2)))
          (Ico 0 (T + δ) ×ˢ c.target) := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact (hfull x0 i j).contMDiffOn
      have hh := hjoint.comp hc
        (fun q hq => ⟨hq.1, c.map_source hq.2⟩)
      have hh' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => (g q.1).inner q.2 (E i q.2) (E j q.2))
          (Ico 0 (T + δ) ×ˢ c.source) :=
        hh.congr (fun q hq => by dsimp only [Function.comp_def]; rw [c.left_inv hq.2])
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hh'
    have hsum : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞
        (fun q : ℝ × M => ∑ i : Fin n, ∑ j : Fin n,
          (g q.1).inner q.2 (E i q.2) (E j q.2) • P i j)
        (Ico 0 (T + δ) ×ˢ e.baseSet) :=
      contMDiffOn_finsetSum (fun i _ => contMDiffOn_finsetSum (fun j _ =>
        (hscalar i j).smul contMDiffOn_const))
    have hsmall : Ico 0 (T + δ) ×ˢ e.baseSet ∈ 𝓝[Ico 0 (T + δ) ×ˢ univ] p := by
      have hnear : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ e.baseSet :=
        (continuous_snd.tendsto p) (e.open_baseSet.mem_nhds hx0)
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with q hq hy
      exact ⟨hq.1, hy⟩
    have hBC : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞
        BC (Ico 0 (T + δ) ×ˢ univ) p :=
      ((hsum.congr (fun q hq => hBCeq q hq.2)) p ⟨hp.1, hx0⟩).mono_of_mem_nhdsWithin hsmall
    exact (contMDiffWithinAt_hom_bundle (fun q : ℝ × M =>
      (TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ) q.2 ((g q.1).inner q.2) :
        TotalSpace (V →L[ℝ] V →L[ℝ] ℝ)
          (fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)))).mpr
      ⟨contMDiffWithinAt_snd, hBC⟩
  have hequation (t : ℝ) (ht : t ∈ Ico 0 (T + δ))
      (x : M) (v w : TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * (D t).ricci x v w) (Ico 0 (T + δ)) t := by
    by_cases hlt : t < T
    · have hn : Ico 0 T ∈ 𝓝[Ico 0 (T + δ)] t := by
        have hnear : ∀ᶠ s : ℝ in 𝓝 t, s < T := Iio_mem_nhds hlt
        filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with s hs hsT
        exact ⟨hs.1, hsT⟩
      rw [hDl t hlt]
      apply ((F.equation t ⟨ht.1, hlt⟩ x v w).mono_of_mem_nhdsWithin hn).congr_of_eventuallyEq_of_mem _ ht
      filter_upwards [hn] with s hs
      rw [hgl s hs.2]
    · by_cases he : t = T
      · subst t
        let c := chartAt V x
        let e := trivializationAt V (TangentSpace (𝓡 n)) x
        let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        let E := e.localFrame cb
        have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt V (TangentSpace (𝓡 n)) x
        let b := e.basisAt cb hx
        have hcx : c.symm (c x) = x := c.left_inv (mem_chart_source V x)
        have hcxt : c x ∈ c.target := c.map_source (mem_chart_source V x)
        have hE (i : Fin n) : E i x = b i := e.localFrame_apply_of_mem_baseSet cb hx
        have hd (i j : Fin n) : DifferentiableAt ℝ
            (fun s => (g s).inner x (b i) (b j)) T := by
          have hn : Ioo (T / 2) (T + δ) ×ˢ c.target ∈ 𝓝 (T, c x) :=
            prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
              (c.open_target.mem_nhds hcxt)
          have hh : ContDiffAt ℝ ∞ (fun s => (g s).inner (c.symm (c x))
              (E i (c.symm (c x))) (E j (c.symm (c x)))) T :=
            ((hmid x i j).contDiffAt hn).comp T (contDiffAt_id.prodMk contDiffAt_const)
          apply (hh.differentiableAt (by simp)).congr_of_eventuallyEq
          apply Eventually.of_forall
          intro s
          symm
          calc
            _ = (g s).inner x (E i x) (E j x) :=
              congrArg (fun y : M => (g s).inner y (E i y) (E j y)) hcx
            _ = _ := by rw [hE i, hE j]
        have hexpand (s : ℝ) : (g s).inner x v w =
            ∑ j : Fin n, ∑ i : Fin n,
              b.repr w j * (b.repr v i * (g s).inner x (b i) (b j)) := by
          calc
            _ = (g s).inner x (∑ i : Fin n, b.repr v i • b i)
                (∑ j : Fin n, b.repr w j • b j) := by rw [b.sum_repr, b.sum_repr]
            _ = _ := by simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
              Finset.mul_sum]
        have hdiff : DifferentiableAt ℝ (fun s => (g s).inner x v w) T := by
          have hh : DifferentiableAt ℝ (fun s => ∑ j : Fin n, ∑ i : Fin n,
              b.repr w j * (b.repr v i * (g s).inner x (b i) (b j))) T :=
            DifferentiableAt.fun_sum (fun j _ => DifferentiableAt.fun_sum (fun i _ =>
              ((hd i j).const_mul _).const_mul _))
          exact hh.congr_of_eventuallyEq (Eventually.of_forall hexpand)
        have hright : HasDerivWithinAt (fun s => (g s).inner x v w)
            (-2 * (G.connection T).ricci x v w) (Ico T (T + δ)) T := by
          apply (G.equation T ⟨le_rfl, by linarith⟩ x v w).congr_of_mem
          · intro s hs
            rw [hgr s hs.1]
          · exact ⟨le_rfl, by linarith⟩
        have heq := UniqueDiffWithinAt.eq_deriv (Ico T (T + δ))
          (uniqueDiffOn_Ico T (T + δ) T ⟨le_rfl, by linarith⟩)
          hright hdiff.hasDerivAt.hasDerivWithinAt
        rw [hDr T le_rfl]
        exact (hdiff.hasDerivAt.congr_deriv heq.symm).hasDerivWithinAt
      · have hgt : T < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        have hn : Ico T (T + δ) ∈ 𝓝[Ico 0 (T + δ)] t := by
          have hnear : ∀ᶠ s : ℝ in 𝓝 t, T < s := Ioi_mem_nhds hgt
          filter_upwards [self_mem_nhdsWithin,
            Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with s hs hsT
          exact ⟨hsT.le, hs.2⟩
        rw [hDr t hgt.le]
        apply ((G.equation t ⟨hgt.le, ht.2⟩ x v w).mono_of_mem_nhdsWithin hn).congr_of_eventuallyEq_of_mem _ ht
        filter_upwards [hn] with s hs
        rw [hgr s hs.1]
  let H : RicciFlow n M (Ico 0 (T + δ)) :=
    { metric := g
      connection := D
      interval := ordConnected_Ico
      nontrivial := ⟨0, ⟨le_rfl, by linarith⟩, T, ⟨hT.le, by linarith⟩, hT.ne⟩
      smooth := hsmooth
      equation := hequation }
  refine ⟨H, ?_, ?_⟩
  · intro t ht
    exact (hgl t ht.2).symm
  · intro t ht
    exact (hgr t ht.1).symm


theorem exists_ricciFlow_time_translate
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {δ : ℝ} (hδ : 0 < δ) (R : RicciFlow n M (Ico 0 δ)) (T : ℝ) :
    ∃ G : RicciFlow n M (Ico T (T + δ)), ∀ t, G.metric t = R.metric (t - T) := by
  have hmap : MapsTo (fun s : ℝ => s - T) (Ico T (T + δ)) (Ico 0 δ) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let G : RicciFlow n M (Ico T (T + δ)) :=
    { metric := fun t => R.metric (t - T)
      connection := fun t => R.connection (t - T)
      interval := ordConnected_Ico
      nontrivial := ⟨T, ⟨le_rfl, by linarith⟩, T + δ / 2,
        ⟨by linarith, by linarith⟩, by linarith⟩
      smooth := by
        have hsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
            (fun p : ℝ × M => (p.1 - T, p.2)) (Ico T (T + δ) ×ˢ univ) :=
          (contMDiffOn_fst.sub contMDiffOn_const).prodMk contMDiffOn_snd
        exact R.smooth.comp hsm (fun p hp => ⟨hmap hp.1, hp.2⟩)
      equation := by
        intro t ht x v w
        have hh := (R.equation (t - T) (hmap ht) x v w).comp t
          ((hasDerivAt_id t).sub_const T).hasDerivWithinAt hmap
        simpa only [Function.comp_def, id_eq, mul_one] using hh }
  exact ⟨G, fun _ => rfl⟩

end EndpointGluing

end PoincareConjecture.Proofs.M03
