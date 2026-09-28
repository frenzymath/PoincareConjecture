import PoincareConjecture.Proofs.M09.EndpointFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Topology
open Set Filter

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1200000 in

theorem exists_parametric_smooth_endpoint_family
    (γ : P × ℝ → M) (D : Set (P × ℝ)) (hD : IsOpen D)
    (hγ : ContMDiffOn (𝓘(ℝ, P × ℝ)) (𝓡 n) ∞ γ D)
    (a0 : P) (hI : ∀ r ∈ Set.Icc (0 : ℝ) 1, (a0, r) ∈ D) :
    let e := chartAt E (γ (a0, 1))
    ∃ (f : (P × E) × ℝ → M) (Ω : Set ((P × E) × ℝ))
        (V : Set (P × E)) (W : Set P),
      IsOpen Ω ∧ IsOpen V ∧ IsOpen W ∧ a0 ∈ W ∧
      (a0, e (γ (a0, 1))) ∈ V ∧ V ⊆ W ×ˢ e.target ∧
      V ×ˢ Set.Icc (0 : ℝ) 1 ⊆ Ω ∧
      ContMDiffOn (𝓘(ℝ, (P × E) × ℝ)) (𝓡 n) ∞ f Ω ∧
      (∀ a y, f ((a, y), 0) = γ (a, 0)) ∧
      (∀ a y, f ((a, y), 1) = e.symm y) ∧
      W ×ˢ Set.Icc (0 : ℝ) 1 ⊆ D ∧
      (∀ a ∈ W, (a, e (γ (a, 1))) ∈ V) ∧
      ∀ a ∈ W, ∀ r ∈ Set.Icc (0 : ℝ) 1,
        f ((a, e (γ (a, 1))), r) = γ (a, r) := by
  classical
  let e := chartAt E (γ (a0, 1))
  let y0 : E := e (γ (a0, 1))
  let D0 := D ∩ γ ⁻¹' e.source
  have hD0 : IsOpen D0 := hγ.continuousOn.isOpen_inter_preimage hD e.open_source
  have ha1 : (a0, (1 : ℝ)) ∈ D0 :=
    ⟨hI 1 ⟨zero_le_one, le_rfl⟩, mem_chart_source E (γ (a0, 1))⟩
  have h1 : (1 : ℝ) ∈ (fun r : ℝ ↦ (a0, r)) ⁻¹' D0 := ha1
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hD0.preimage (continuous_const.prodMk continuous_id)).mem_nhds h1)
  obtain ⟨d, hld, hd1⟩ := exists_between (max_lt (show (0 : ℝ) < 1 by norm_num) hlu.1)
  have hd0 : 0 < d := (le_max_left 0 l).trans_lt hld
  have hld' : l < d := (le_max_right 0 l).trans_lt hld
  have htail : ∀ r ∈ Set.Icc d 1, (a0, r) ∈ D0 :=
    fun r hr ↦ hsub ⟨hld'.trans_le hr.1, hr.2.trans_lt hlu.2⟩
  have hdisjoint : Disjoint (Set.Iic d) ({1} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro r hr hr1
    exact (not_le_of_gt hd1) ((Set.mem_singleton_iff.mp hr1) ▸ hr)
  obtain ⟨χ, hzero, hone, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, ℝ))
      isClosed_Iic isClosed_singleton hdisjoint (n := ⊤)
  have hχzero (r : ℝ) (hr : r ≤ d) : χ r = 0 := by
    have h : ∀ᶠ t in 𝓝 r, χ t = 0 :=
      (nhds_le_nhdsSet (show r ∈ Set.Iic d from hr)) hzero
    exact h.self_of_nhds
  have hχone : χ (1 : ℝ) = 1 := by
    have h : ∀ᶠ t in 𝓝 (1 : ℝ), χ t = 1 :=
      (nhds_le_nhdsSet (Set.mem_singleton 1)) hone
    exact h.self_of_nhds
  let k : (P × E) × ℝ → E := fun z ↦
    e (γ (z.1.1, z.2)) + χ z.2 • (z.1.2 - e (γ (z.1.1, 1)))
  let f : (P × E) × ℝ → M := fun z ↦
    if d < z.2 then e.symm (k z) else γ (z.1.1, z.2)
  let Ω0 : Set ((P × E) × ℝ) :=
    (fun z ↦ (z.1.1, z.2)) ⁻¹' D0 ∩ (fun z ↦ (z.1.1, (1 : ℝ))) ⁻¹' D0
  let Ω1 := Ω0 ∩ k ⁻¹' e.target
  let L : Set ((P × E) × ℝ) :=
    (fun z ↦ (z.1.1, z.2)) ⁻¹' D ∩ Prod.snd ⁻¹' Set.Iio d
  let Ω := L ∪ Ω1
  have hΩ0 : IsOpen Ω0 :=
    (hD0.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
      (hD0.preimage (continuous_fst.fst.prodMk continuous_const))
  have hbase : ContMDiffOn (𝓘(ℝ, (P × E) × ℝ)) (𝓡 n) ∞
      (fun z ↦ γ (z.1.1, z.2)) Ω0 :=
    hγ.comp (contDiff_fst.fst.prodMk contDiff_snd).contMDiff.contMDiffOn
      (fun z hz ↦ hz.1.1)
  have hend : ContMDiffOn (𝓘(ℝ, (P × E) × ℝ)) (𝓡 n) ∞
      (fun z ↦ γ (z.1.1, 1)) Ω0 :=
    hγ.comp (contDiff_fst.fst.prodMk contDiff_const).contMDiff.contMDiffOn
      (fun z hz ↦ hz.2.1)
  have hcoord : ContDiffOn ℝ ∞ (fun z : (P × E) × ℝ ↦ e (γ (z.1.1, z.2))) Ω0 :=
    (contMDiffOn_chart.comp hbase (fun z hz ↦ hz.1.2)).contDiffOn
  have hcoordEnd : ContDiffOn ℝ ∞ (fun z : (P × E) × ℝ ↦ e (γ (z.1.1, 1))) Ω0 :=
    (contMDiffOn_chart.comp hend (fun z hz ↦ hz.2.2)).contDiffOn
  have hχ : ContDiff ℝ ∞ (fun z : (P × E) × ℝ ↦ χ z.2) :=
    χ.contMDiff.contDiff.comp contDiff_snd
  have hk : ContDiffOn ℝ ∞ k Ω0 :=
    hcoord.add (hχ.contDiffOn.smul (contDiff_fst.snd.contDiffOn.sub hcoordEnd))
  have hΩ1 : IsOpen Ω1 := hk.continuousOn.isOpen_inter_preimage hΩ0 e.open_target
  have hL : IsOpen L := (hD.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
    (isOpen_Iio.preimage continuous_snd)
  have hfL : ContMDiffOn (𝓘(ℝ, (P × E) × ℝ)) (𝓡 n) ∞ f L := by
    apply (hγ.comp (contDiff_fst.fst.prodMk contDiff_snd).contMDiff.contMDiffOn
      (fun z hz ↦ hz.1)).congr
    intro z hz
    have hzlt : z.2 < d := hz.2
    simp only [f, if_neg (not_lt.mpr hzlt.le), Function.comp_apply]
  have hf1 : ContMDiffOn (𝓘(ℝ, (P × E) × ℝ)) (𝓡 n) ∞ f Ω1 := by
    have hcomp := (contMDiffOn_chart_symm (I := 𝓡 n) (x := γ (a0, 1))).comp
      (hk.mono Set.inter_subset_left).contMDiffOn (fun z hz ↦ hz.2)
    apply hcomp.congr
    intro z hz
    change f z = e.symm (k z)
    by_cases hr : d < z.2
    · simp only [f, if_pos hr]
    · simp only [f, if_neg hr, k, hχzero z.2 (le_of_not_gt hr), zero_smul, add_zero]
      exact (e.left_inv hz.1.1.2).symm
  have hΩ : IsOpen Ω := hL.union hΩ1
  have hf : ContMDiffOn (𝓘(ℝ, (P × E) × ℝ)) (𝓡 n) ∞ f Ω :=
    hfL.union_of_isOpen hf1 hL hΩ1
  have hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, ((a0, y0), r) ∈ Ω := by
    intro r hr
    by_cases hrd : r < d
    · exact Or.inl ⟨hI r hr, hrd⟩
    · apply Or.inr
      have hr0 := htail r ⟨le_of_not_gt hrd, hr.2⟩
      refine ⟨⟨hr0, ha1⟩, ?_⟩
      change k ((a0, y0), r) ∈ e.target
      simpa only [k, y0, sub_self, smul_zero, add_zero] using e.map_source hr0.2
  have hnear : ∀ᶠ z : P × E in 𝓝 (a0, y0),
      ∀ r ∈ Set.Icc (0 : ℝ) 1, (z, r) ∈ Ω := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact hΩ.mem_nhds (hsegment r hr)
  obtain ⟨V0, hVsub, hV0, hzV0⟩ := mem_nhds_iff.mp hnear
  have hwhole : ∀ᶠ a in 𝓝 a0, ∀ r ∈ Set.Icc (0 : ℝ) 1, (a, r) ∈ D := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact hD.mem_nhds (hI r hr)
  have htailNear : ∀ᶠ a in 𝓝 a0, ∀ r ∈ Set.Icc d 1, (a, r) ∈ D0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact hD0.mem_nhds (htail r hr)
  have hendAt : ContMDiffAt (𝓘(ℝ, P)) (𝓡 n) ∞ (fun a ↦ γ (a, 1)) a0 :=
    (hγ.contMDiffAt (hD.mem_nhds ha1.1)).comp a0
      (contMDiffAt_id.prodMk_space contMDiffAt_const)
  have hgraph : ContinuousAt (fun a : P ↦ (a, e (γ (a, 1)))) a0 :=
    continuousAt_id.prodMk ((contMDiffOn_chart.contMDiffAt
      (e.open_source.mem_nhds ha1.2)).comp a0 hendAt).continuousAt
  have hgraphNear : ∀ᶠ a in 𝓝 a0, (a, e (γ (a, 1))) ∈ V0 :=
    hgraph.preimage_mem_nhds (hV0.mem_nhds hzV0)
  obtain ⟨W, hWsub, hW, haW⟩ :=
    mem_nhds_iff.mp (hwhole.and (htailNear.and hgraphNear))
  let V := V0 ∩ (W ×ˢ e.target)
  have hV : IsOpen V := hV0.inter (hW.prod e.open_target)
  have hzV : (a0, y0) ∈ V := ⟨hzV0, haW, e.map_source ha1.2⟩
  refine ⟨f, Ω, V, W, hΩ, hV, hW, haW, hzV, Set.inter_subset_right,
    (fun z hz ↦ hVsub hz.1.1 z.2 hz.2), hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro a y
    simp only [f, if_neg (not_lt.mpr hd0.le)]
  · intro a y
    change f ((a, y), 1) = e.symm y
    simp only [f, if_pos hd1, k, hχone, one_smul, add_sub_cancel]
  · intro z hz
    exact (hWsub hz.1).1 z.2 hz.2
  · intro a ha
    exact ⟨(hWsub ha).2.2, ha, e.map_source ((hWsub ha).2.1 1 ⟨hd1.le, le_rfl⟩).2⟩
  · intro a ha r hr
    change f ((a, e (γ (a, 1))), r) = γ (a, r)
    by_cases hrd : d < r
    · simp only [f, if_pos hrd, k, sub_self, smul_zero, add_zero]
      exact e.left_inv ((hWsub ha).2.1 r ⟨hrd.le, hr.2⟩).2
    · simp only [f, if_neg hrd]

end PoincareConjecture.Proofs.M09
