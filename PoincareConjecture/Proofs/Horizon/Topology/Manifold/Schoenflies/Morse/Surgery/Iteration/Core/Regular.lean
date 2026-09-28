import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.AuxiliaryHeight
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.AnnularRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Extrema
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.ComponentBand
import Mathlib.Topology.MetricSpace.Thickening



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

namespace SphereSurgeryCoreCap

variable {v : E3} {g : S2 → E3} {B : Set Real}



theorem exists_annular_core_of_regular
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) {a b : Real} (hab : a < b)
    (hbounds : ∀ p ∈ C, inner Real v (g p) ∈ Icc a b)
    (ha : ∃ p ∈ C, inner Real v (g p) = a)
    (hb : ∃ p ∈ C, inner Real v (g p) = b)
    (hregular : ∀ p ∈ C,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → inner Real v (g (F (q, t))) = t) ∧
      C = F '' (univ ×ˢ Icc a b) := by
  obtain ⟨h, hh, hactual, hreg, _⟩ :=
    exists_regular_auxiliary_height L hpair hg hcore a b hregular
  obtain ⟨p, hp, hpa⟩ := ha
  have hpa' : h p = a := (hactual p hp).eq_of_nhds.trans hpa
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, _, hband⟩ :=
    exists_smooth_regular_band_component_of_smooth hh hab hreg p hpa'
  have hactualC : EqOn h (fun q => inner Real v (g q)) C :=
    fun q hq => (hactual q hq).eq_of_nhds
  have hcover : C ⊆ F '' (univ ×ˢ Icc a b) := by
    rw [hband]
    apply hC.subset_connectedComponentIn hp
    intro q hq
    change h q ∈ Icc a b
    rw [hactualC hq]
    exact hbounds q hq
  have hcoreF : C = F '' (univ ×ˢ Icc a b) :=
    core_eq_annular_band L hpair hcore hC F hδ hFs hF hFi hh.continuous.continuousOn
      hheight hactualC hcover ⟨p, hp, hpa'⟩ (by
        obtain ⟨q, hq, hqb⟩ := hb
        exact ⟨q, hq, (hactualC hq).trans hqb⟩)
  let V : Set S2 := interior {q : S2 | h q = inner Real v (g q)}
  have hCV : C ⊆ V := fun q hq => mem_interior_iff_mem_nhds.mpr (hactual q hq)
  let U : Set (S1 × Real) := F.source ∩ F ⁻¹' V
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_interior
  have hKU : univ ×ˢ Icc a b ⊆ U := by
    rintro ⟨q, t⟩ hqt
    refine ⟨hFs ▸ ⟨mem_univ _, ⟨by linarith [hqt.2.1], by linarith [hqt.2.2]⟩⟩, ?_⟩
    exact hCV (hcoreF ▸ mem_image_of_mem F hqt)
  obtain ⟨ε, hε, hthick⟩ :=
    (isCompact_univ.prod isCompact_Icc).exists_thickening_subset_open hU hKU
  let S : Set (S1 × Real) := univ ×ˢ Ioo (a - ε) (b + ε)
  have hSU : S ⊆ U := by
    rintro ⟨q, t⟩ hqt
    apply hthick
    by_cases hta : t < a
    · apply mem_thickening_iff.mpr
      refine ⟨(q, a), ⟨mem_univ _, ⟨le_rfl, hab.le⟩⟩, ?_⟩
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_neg (sub_neg.mpr hta),
        max_eq_right (by linarith : 0 ≤ -(t - a))]
      linarith [hqt.2.1]
    · by_cases hbt : b < t
      · apply mem_thickening_iff.mpr
        refine ⟨(q, b), ⟨mem_univ _, ⟨hab.le, le_rfl⟩⟩, ?_⟩
        simp only [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_pos (sub_pos.mpr hbt),
          max_eq_right (by linarith : 0 ≤ t - b)]
        linarith [hqt.2.2]
      · exact self_subset_thickening hε _ ⟨mem_univ _, ⟨le_of_not_gt hta, le_of_not_gt hbt⟩⟩
  have hSs : S ⊆ F.source := hSU.trans inter_subset_left
  let G := F.restrOpen S (isOpen_univ.prod isOpen_Ioo)
  have hGs : G.source = S := by
    exact inter_eq_right.mpr hSs
  refine ⟨ε, hε, G, hGs, hF.mono (show G.source ⊆ F.source from inter_subset_left),
    hFi.mono (show G.target ⊆ F.target from inter_subset_left), ?_, ?_⟩
  · intro q t ht
    have hqt : (q, t) ∈ S := ⟨mem_univ _, ht⟩
    have hV : F (q, t) ∈ V := (hSU hqt).2
    have heq := (interior_subset : V ⊆ {q : S2 | h q = inner Real v (g q)}) hV
    exact heq.symm.trans (hheight q t (hFs ▸ hSs hqt).2)
  · exact hcoreF

end SphereSurgeryCoreCap

namespace SphereSurgeryPath



theorem exists_annular_core_of_regular
    {v : E3} {f g : S2 → E3} (P : SphereSurgeryPath v f g)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hcaps : P.PreservesCaps) {B : Set Real}
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hregular : ∀ p ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ D ∈ L, ∃ E ∈ L, D.center < E.center ∧
      ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
        F.source = univ ×ˢ Ioo (D.center - δ) (E.center + δ) ∧
        ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
        ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
        (∀ q t, t ∈ Ioo (D.center - δ) (E.center + δ) →
          inner Real v (g (F (q, t))) = t) ∧
        P.core = F '' (univ ×ˢ Icc D.center E.center) := by
  obtain ⟨D, hD, E, hE, ha, hb, hbounds, hlt, _, _⟩ :=
    P.exists_cap_height_bounds_of_regular hg hcaps L hpair hcore hregular
  exact ⟨D, hD, E, hE, hlt,
    SphereSurgeryCoreCap.exists_annular_core_of_regular L hpair hg hcore
      (P.isConnected_core hcaps).isPreconnected hlt hbounds ha hb hregular⟩

end SphereSurgeryPath

end Poincare.Manifold.Schoenflies
