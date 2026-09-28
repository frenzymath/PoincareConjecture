import PoincareConjecture.Proofs.M76.Rigidity.MeridianParameter










set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem isEmbedding_hamiltonMeridianParameter_of_chart
    {a b : ℝ} (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hKbox : K.space = D ×ˢ Icc a b)
    (c : OpenPartialHomeomorph (D × ℝ) H)
    (hcs : univ ×ˢ Icc a b ⊆ c.source)
    (hc : ∀ w : D × ℝ, c w = hamiltonMeridianCutMap w) :
    Topology.IsEmbedding (fun z : K.space => hamiltonMeridianParameter z) := by
  let Q := latticeHandleDomainEquiv (Fin 2) (Fin 1) L
  let : T2Space R := (Q.trans ((Homeomorph.refl D).prodCongr
    hamiltonSolidTorusCircleEquiv)).isEmbedding.t2Space
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hcont : Continuous (fun z : K.space => hamiltonMeridianParameter z) :=
    (continuousOn_hamiltonMeridianParameter.mono
      (fun z hz => ⟨(hKbox.subset hz).1, mem_univ _⟩)).domRestrict
  apply (hcont.isClosedEmbedding ?_).isEmbedding
  intro z w heq
  let z' : D × ℝ := (⟨z.1.1, (hKbox.subset z.property).1⟩, z.1.2)
  let w' : D × ℝ := (⟨w.1.1, (hKbox.subset w.property).1⟩, w.1.2)
  have hz' : z' ∈ c.source := hcs ⟨mem_univ _, (hKbox.subset z.property).2⟩
  have hw' : w' ∈ c.source := hcs ⟨mem_univ _, (hKbox.subset w.property).2⟩
  have hcw : c z' = c w' := by
    rw [hc, hc]
    exact (hamiltonMeridianParameter_domainEquiv z'.1 z'.2).symm.trans
      ((congrArg Q heq).trans (hamiltonMeridianParameter_domainEquiv w'.1 w'.2))
  have hzw := c.injOn hz' hw' hcw
  exact Subtype.ext (congrArg (fun v : D × ℝ => ((v.1 : V2), v.2)) hzw)




theorem hamiltonMeridianParameter_range_mem_nhds_of_chart
    {a b : ℝ} (K : SimplicialComplex ℝ E)
    (hKbox : K.space = D ×ˢ Icc a b)
    (c : OpenPartialHomeomorph (D × ℝ) H)
    (hcs : univ ×ˢ Icc a b ⊆ c.source)
    (hc : ∀ w : D × ℝ, c w = hamiltonMeridianCutMap w)
    (x : D) {t : ℝ} (ht : t ∈ Ioo a b) :
    range (fun z : K.space => hamiltonMeridianParameter z) ∈
      𝓝 (hamiltonMeridianParameter (x, t)) := by
  let Q := latticeHandleDomainEquiv (Fin 2) (Fin 1) L
  let U : Set R := Q ⁻¹' (c '' (univ ×ˢ Ioo a b))
  have hU : IsOpen U :=
    (c.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
      ((prod_mono subset_rfl Ioo_subset_Icc_self).trans hcs)).preimage Q.continuous
  have hxU : hamiltonMeridianParameter (x, t) ∈ U := by
    refine ⟨(x, t), ⟨mem_univ _, ht⟩, ?_⟩
    exact (hc (x, t)).trans (hamiltonMeridianParameter_domainEquiv x t).symm
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  obtain ⟨w, hw, heq⟩ := hy
  have hwK : ((w.1 : V2), w.2) ∈ K.space :=
    hKbox.symm.subset ⟨w.1.property, hw.2.1.le, hw.2.2.le⟩
  refine ⟨⟨((w.1 : V2), w.2), hwK⟩, ?_⟩
  apply Q.injective
  exact (hamiltonMeridianParameter_domainEquiv w.1 w.2).trans ((hc w).symm.trans heq)



noncomputable def hamiltonMeridianWideBicollar : OpenPartialHomeomorph (D × ℝ) H :=
  (OpenPartialHomeomorph.refl D).prod
    ((AddCircle.shortArcQuotient p 2).trans
      hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph)



theorem hamiltonMeridianWideBicollar_source :
    hamiltonMeridianWideBicollar.source = univ ×ˢ Ioo (-2 : ℝ) 2 := by
  change univ ×ˢ ((AddCircle.shortArcQuotient p 2).trans
    hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph).source = _
  rw [OpenPartialHomeomorph.trans_source]
  change univ ×ˢ ((AddCircle.shortArcQuotient p 2).source ∩
    (AddCircle.shortArcQuotient p 2) ⁻¹' univ) = _
  rw [preimage_univ, inter_univ, AddCircle.shortArcQuotient_source p (by norm_num)]



theorem hamiltonMeridianWideBicollar_apply (w : D × ℝ) :
    hamiltonMeridianWideBicollar w = hamiltonMeridianCutMap w := rfl





theorem exists_hamiltonMeridian_short_box (x : R) :
    ∃ (a b : ℝ) (K : SimplicialComplex ℝ E) (z : K.space),
      a < b ∧ K.faces.Finite ∧ K.space = D ×ˢ Icc a b ∧
      hamiltonMeridianParameter z = x ∧
      Topology.IsEmbedding (fun u : K.space => hamiltonMeridianParameter u) ∧
      range (fun u : K.space => hamiltonMeridianParameter u) ∈ 𝓝 x ∧
      ((a = -1 ∧ b = 1) ∨ (0 < a ∧ b < p)) := by
  let Q := latticeHandleDomainEquiv (Fin 2) (Fin 1) L
  let y : H := Q x
  obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico (hamiltonSolidTorusCircleEquiv y.2)
  have hqt : hamiltonMeridianParameter ((y.1 : V2), t) = x := by
    apply Q.injective
    rw [hamiltonMeridianParameter_domainEquiv]
    change (y.1, hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p)) = y
    rw [he, hamiltonSolidTorusCircleEquiv.symm_apply_apply]
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨K, hK, hKbox⟩ := exists_finite_hamiltonMeridianBox
      (show (-1 : ℝ) < 1 by norm_num)
    have hzK : ((y.1 : V2), (0 : ℝ)) ∈ K.space :=
      hKbox.symm.subset ⟨y.1.property, by norm_num⟩
    have hcs : univ ×ˢ Icc (-1 : ℝ) 1 ⊆ hamiltonMeridianWideBicollar.source := by
      rw [hamiltonMeridianWideBicollar_source]
      intro w hw
      exact ⟨mem_univ _, by linarith [hw.2.1], by linarith [hw.2.2]⟩
    have hnbhd := hamiltonMeridianParameter_range_mem_nhds_of_chart K hKbox
      hamiltonMeridianWideBicollar hcs hamiltonMeridianWideBicollar_apply y.1
      (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)
    rw [hqt] at hnbhd
    exact ⟨-1, 1, K, ⟨_, hzK⟩, by norm_num, hK, hKbox, hqt,
      isEmbedding_hamiltonMeridianParameter_of_chart K hK hKbox
        hamiltonMeridianWideBicollar hcs hamiltonMeridianWideBicollar_apply,
      hnbhd, Or.inl ⟨rfl, rfl⟩⟩
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    let a := t / 2
    let b := (t + p) / 2
    have hat : a < t := by dsimp [a]; linarith
    have htb : t < b := by dsimp [b]; linarith [ht.2]
    have ha : 0 < a := by dsimp [a]; linarith
    have hb : b < p := by dsimp [b]; linarith [ht.2]
    obtain ⟨K, hK, hKbox⟩ := exists_finite_hamiltonMeridianBox (hat.trans htb)
    have hzK : ((y.1 : V2), t) ∈ K.space :=
      hKbox.symm.subset ⟨y.1.property, hat.le, htb.le⟩
    have hcs : univ ×ˢ Icc a b ⊆ hamiltonMeridianOpenCut.source := by
      rw [hamiltonMeridianOpenCut_source]
      intro w hw
      exact ⟨mem_univ _, ha.trans_le hw.2.1, hw.2.2.trans_lt hb⟩
    have hnbhd := hamiltonMeridianParameter_range_mem_nhds_of_chart K hKbox
      hamiltonMeridianOpenCut hcs hamiltonMeridianOpenCut_apply y.1 ⟨hat, htb⟩
    rw [hqt] at hnbhd
    exact ⟨a, b, K, ⟨_, hzK⟩, hat.trans htb, hK, hKbox, hqt,
      isEmbedding_hamiltonMeridianParameter_of_chart K hK hKbox
        hamiltonMeridianOpenCut hcs hamiltonMeridianOpenCut_apply,
      hnbhd, Or.inr ⟨ha, hb⟩⟩

end PoincareConjecture.M76
