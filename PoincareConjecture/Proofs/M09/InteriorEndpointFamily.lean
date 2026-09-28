import PoincareConjecture.Proofs.M09.EndpointFamily








set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Filter

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "C" => EuclideanSpace ℝ (Fin n)

theorem exists_smooth_interior_endpoint_family (f : E × ℝ → M) (U : Set (E × ℝ))
    (hU : IsOpen U) (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (x0 : E) (L c : ℝ) (hc : c ∈ Set.Ioo 0 L)
    (hsegment : ∀ s ∈ Set.Icc 0 L, (x0, s) ∈ U) :
    let e := chartAt C (f (x0, c))
    ∃ (Φ : (E × C) × ℝ → M) (Ω : Set ((E × C) × ℝ)) (N : Set (E × C)),
      IsOpen Ω ∧ IsOpen N ∧ (x0, e (f (x0, c))) ∈ N ∧
      N ×ˢ Set.Icc 0 L ⊆ Ω ∧ ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞ Φ Ω ∧
      (∀ z ∈ N, z.2 ∈ e.target ∧ ∀ s ∈ Set.Icc 0 L, (z.1, s) ∈ U) ∧
      (∀ x y, Φ ((x, y), 0) = f (x, 0)) ∧
      (∀ x y, Φ ((x, y), L) = f (x, L)) ∧
      (∀ x y, Φ ((x, y), c) = e.symm y) ∧
      ∀ z ∈ N, ∀ s ∈ Set.Icc 0 L, Φ ((z.1, e (f (z.1, c))), s) = f (z.1, s) := by
  classical
  let e := chartAt C (f (x0, c))
  let a : E → C := fun x ↦ e (f (x, c))
  let D := U ∩ f ⁻¹' e.source
  have hD : IsOpen D := hf.continuousOn.isOpen_inter_preimage hU e.open_source
  have hxc : (x0, c) ∈ D :=
    ⟨hsegment c (Set.Ioo_subset_Icc_self hc), mem_chart_source C (f (x0, c))⟩
  obtain ⟨V0, W0, hV0, hxV0, hW0, hcW0, hbox⟩ :=
    mem_nhds_prod_iff'.mp (hD.mem_nhds hxc)
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hW0.inter isOpen_Ioo).mem_nhds (show c ∈ W0 ∩ Set.Ioo 0 L from ⟨hcW0, hc⟩))
  have hrI : Set.Icc (c - r) (c + r) ⊆ W0 ∩ Set.Ioo 0 L := by
    simpa only [Real.closedBall_eq_Icc] using hrsub
  have hrc : r < c := by
    have h := (hrI (show c - r ∈ Set.Icc (c - r) (c + r) from ⟨le_rfl, by linarith⟩)).2.1
    linarith
  have hcr : c + r < L :=
    (hrI (show c + r ∈ Set.Icc (c - r) (c + r) from ⟨by linarith, le_rfl⟩)).2.2
  have hnear : ∀ᶠ x in 𝓝 x0, ∀ s ∈ Set.Icc 0 L, (x, s) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    exact hU.mem_nhds (hsegment s hs)
  obtain ⟨V1, hV1sub, hV1, hxV1⟩ := mem_nhds_iff.mp hnear
  let V := V0 ∩ V1
  have hV : IsOpen V := hV0.inter hV1
  have hxV : x0 ∈ V := ⟨hxV0, hxV1⟩
  have hfull (x : E) (hx : x ∈ V) (s : ℝ) (hs : s ∈ Set.Icc 0 L) : (x, s) ∈ U :=
    hV1sub hx.2 s hs
  have hband (x : E) (hx : x ∈ V) (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) :
      (x, s) ∈ U ∧ f (x, s) ∈ e.source := hbox ⟨hx.1, (hrI hs).1⟩
  have hcI : c ∈ Set.Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  have hdis : Disjoint (Set.Ioo (c - r / 2) (c + r / 2))ᶜ ({c} : Set ℝ) := by
    apply Set.disjoint_left.mpr
    intro s hs heq
    rcases Set.mem_singleton_iff.mp heq with rfl
    exact hs ⟨by linarith, by linarith⟩
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ)) isOpen_Ioo.isClosed_compl isClosed_singleton hdis (n := ⊤)
  have hχzero (s : ℝ) (hs : s ∉ Set.Ioo (c - r / 2) (c + r / 2)) : χ s = 0 := by
    have h : ∀ᶠ t in 𝓝 s, χ t = 0 :=
      (nhds_le_nhdsSet (show s ∈ (Set.Ioo (c - r / 2) (c + r / 2))ᶜ from hs)) hzero
    exact h.self_of_nhds
  have hχone : χ c = 1 := by
    have h : ∀ᶠ t in 𝓝 c, χ t = 1 :=
      (nhds_le_nhdsSet (show c ∈ ({c} : Set ℝ) from Set.mem_singleton c)) hone
    exact h.self_of_nhds
  let k : (E × C) × ℝ → C := fun z ↦ e (f (z.1.1, z.2)) + χ z.2 • (z.1.2 - a z.1.1)
  let Φ : (E × C) × ℝ → M := fun z ↦
    if z.2 ∈ Set.Ioo (c - r) (c + r) then e.symm (k z) else f (z.1.1, z.2)
  let B : Set ((E × C) × ℝ) := (V ×ˢ Set.univ) ×ˢ Set.Ioo (c - r) (c + r)
  have hB : IsOpen B := (hV.prod isOpen_univ).prod isOpen_Ioo
  have hbase : ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞
      (fun z ↦ f (z.1.1, z.2)) B :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd).contMDiff.contMDiffOn
      (fun z hz ↦ (hband z.1.1 hz.1.1 z.2 (Set.Ioo_subset_Icc_self hz.2)).1)
  have hcoord : ContDiffOn ℝ ∞ (fun z : (E × C) × ℝ ↦ e (f (z.1.1, z.2))) B :=
    (contMDiffOn_chart.comp hbase
      (fun z hz ↦ (hband z.1.1 hz.1.1 z.2 (Set.Ioo_subset_Icc_self hz.2)).2)).contDiffOn
  have hac : ContDiffOn ℝ ∞ (fun z : (E × C) × ℝ ↦ a z.1.1) B := by
    have hfc : ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞
        (fun z ↦ f (z.1.1, c)) B :=
      hf.comp (contDiff_fst.fst.prodMk contDiff_const).contMDiff.contMDiffOn
        (fun z hz ↦ (hband z.1.1 hz.1.1 c hcI).1)
    exact (contMDiffOn_chart.comp hfc (fun z hz ↦ (hband z.1.1 hz.1.1 c hcI).2)).contDiffOn
  have hχ : ContDiff ℝ ∞ (fun z : (E × C) × ℝ ↦ χ z.2) :=
    χ.contMDiff.contDiff.comp contDiff_snd
  have hk : ContDiffOn ℝ ∞ k B :=
    hcoord.add (hχ.contDiffOn.smul (contDiff_fst.snd.contDiffOn.sub hac))
  let W := B ∩ k ⁻¹' e.target
  have hW : IsOpen W := hk.continuousOn.isOpen_inter_preimage hB e.open_target
  let A : Set ((E × C) × ℝ) := (Prod.fst ⁻¹' (V ×ˢ Set.univ)) ∩
    (fun z : (E × C) × ℝ ↦ (z.1.1, z.2)) ⁻¹' U
  have hA : IsOpen A := ((hV.prod isOpen_univ).preimage continuous_fst).inter
    (hU.preimage (continuous_fst.fst.prodMk continuous_snd))
  let O := A ∩ (Prod.snd ⁻¹' Set.Icc (c - r / 2) (c + r / 2))ᶜ
  have hO : IsOpen O := hA.inter (isClosed_Icc.preimage continuous_snd).isOpen_compl
  have hfO : ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞ Φ O := by
    have hbaseO : ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞
        (fun z ↦ f (z.1.1, z.2)) O :=
      hf.comp (contDiff_fst.fst.prodMk contDiff_snd).contMDiff.contMDiffOn (fun z hz ↦ hz.1.2)
    apply hbaseO.congr
    intro z hz
    change Φ z = f (z.1.1, z.2)
    by_cases hs : z.2 ∈ Set.Ioo (c - r) (c + r)
    · have hzχ : χ z.2 = 0 := hχzero z.2 (fun ht ↦ hz.2 (Set.Ioo_subset_Icc_self ht))
      simp only [Φ, if_pos hs, k, hzχ, zero_smul, add_zero]
      exact e.left_inv (hband z.1.1 hz.1.1.1 z.2 (Set.Ioo_subset_Icc_self hs)).2
    · simp only [Φ, if_neg hs]
  have hfW : ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞ Φ W := by
    have hcomp := (contMDiffOn_chart_symm (I := 𝓡 n) (x := f (x0, c))).comp
      (hk.mono Set.inter_subset_left).contMDiffOn (fun z hz ↦ hz.2)
    apply hcomp.congr
    intro z hz
    simp only [Φ, if_pos hz.1.2, Function.comp_apply]
    rfl
  let Ω := O ∪ W
  have hΩ : IsOpen Ω := hO.union hW
  have hΦ : ContMDiffOn (𝓘(ℝ, (E × C) × ℝ)) (𝓡 n) ∞ Φ Ω :=
    hfO.union_of_isOpen hfW hO hW
  have hcenter (s : ℝ) (hs : s ∈ Set.Icc 0 L) : ((x0, a x0), s) ∈ Ω := by
    by_cases hsb : s ∈ Set.Ioo (c - r) (c + r)
    · refine Or.inr ⟨⟨⟨hxV, Set.mem_univ _⟩, hsb⟩, ?_⟩
      change k ((x0, a x0), s) ∈ e.target
      simpa only [k, sub_self, smul_zero, add_zero] using
        e.map_source (hband x0 hxV s (Set.Ioo_subset_Icc_self hsb)).2
    · refine Or.inl ⟨⟨⟨hxV, Set.mem_univ _⟩, hsegment s hs⟩, ?_⟩
      intro hsi
      apply hsb
      change s ∈ Set.Icc (c - r / 2) (c + r / 2) at hsi
      exact ⟨by linarith [hsi.1], by linarith [hsi.2]⟩
  have hnearΩ : ∀ᶠ z : E × C in 𝓝 (x0, a x0), ∀ s ∈ Set.Icc 0 L, (z, s) ∈ Ω := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    exact hΩ.mem_nhds (hcenter s hs)
  obtain ⟨N0, hNsub, hN0, hxN0⟩ := mem_nhds_iff.mp hnearΩ
  let N := N0 ∩ (V ×ˢ e.target)
  have hxTarget : a x0 ∈ e.target := e.map_source (mem_chart_source C (f (x0, c)))
  refine ⟨Φ, Ω, N, hΩ, hN0.inter (hV.prod e.open_target), ⟨hxN0, hxV, hxTarget⟩,
    ?_, hΦ, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hNsub hz.1.1 z.2 hz.2
  · intro z hz
    exact ⟨hz.2.2, fun s hs ↦ hfull z.1 hz.2.1 s hs⟩
  · intro x y
    have h0 : (0 : ℝ) ∉ Set.Ioo (c - r) (c + r) := by
      intro h
      linarith [h.1]
    simp only [Φ, if_neg h0]
  · intro x y
    have hL : L ∉ Set.Ioo (c - r) (c + r) := by
      intro h
      linarith [h.2]
    simp only [Φ, if_neg hL]
  · intro x y
    have hcc : c ∈ Set.Ioo (c - r) (c + r) := ⟨by linarith, by linarith⟩
    simp only [Φ, if_pos hcc, k, hχone, one_smul, a, add_sub_cancel]
    rfl
  · intro z hz s _
    change Φ ((z.1, a z.1), s) = f (z.1, s)
    by_cases hsb : s ∈ Set.Ioo (c - r) (c + r)
    · simp only [Φ, if_pos hsb, k, sub_self, smul_zero, add_zero]
      exact e.left_inv (hband z.1 hz.2.1 s (Set.Ioo_subset_Icc_self hsb)).2
    · simp only [Φ, if_neg hsb]

end PoincareConjecture.Proofs.M09
