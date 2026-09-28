import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.NormalizeCaps
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.Ends
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.Orientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.Filling



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

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



theorem exists_ambient_filling_of_capped_annular_core
    (D E : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hDE : D.center < E.center) (hDscale : D.scale < 0) (hEscale : 0 < E.scale)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {δ : Real} (hδ : 0 < δ)
    (hFs : F.source = univ ×ˢ Ioo (D.center - δ) (E.center + δ))
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo (D.center - δ) (E.center + δ) →
      inner Real v (g (F (q, t))) = t)
    (hDboundary : D.chart '' sphere (0 : E2) 1 ⊆ F.target)
    (hEboundary : E.chart '' sphere (0 : E2) 1 ⊆ F.target)
    (hrange : range g = (D.parametrization '' closedBall 0 1) ∪
      (g '' (F '' (univ ×ˢ Icc D.center E.center))) ∪
        (E.parametrization '' closedBall 0 1)) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      G '' sphere (0 : E3) 1 = range g := by
  obtain ⟨α, β, hα, hα1, hβ, hβ1, hleftcut, hrightcut, hrange', hDcircle, hEcircle⟩ :=
    exists_widened_annular_range D E hg hDE hDscale hEscale F hδ hFs hF hFi hheight
      hDboundary hEboundary hrange
  let a := D.center + D.scale * α
  let b := E.center + E.scale * β
  have ha : a < D.center := by dsimp [a]; nlinarith
  have hb : E.center < b := by dsimp [b]; nlinarith
  have hab : a < b := ha.trans (hDE.trans hb)
  let ε := min (a - (D.center - δ)) ((E.center + δ) - b) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr hleftcut.1) (sub_pos.mpr hrightcut.2))
  have hεa : ε < a - (D.center - δ) := by
    dsimp [ε]
    have hh := sub_pos.mpr hleftcut.1
    change 0 < a - (D.center - δ) at hh
    linarith [min_le_left (a - (D.center - δ)) ((E.center + δ) - b)]
  have hεb : ε < (E.center + δ) - b := by
    dsimp [ε]
    have hh := sub_pos.mpr hrightcut.2
    change 0 < (E.center + δ) - b at hh
    linarith [min_le_right (a - (D.center - δ)) ((E.center + δ) - b)]
  let S : Set (S1 × Real) := univ ×ˢ Ioo (a - ε) (b + ε)
  have hSs : S ⊆ F.source := by
    rintro ⟨q, t⟩ hqt
    rw [hFs]
    exact ⟨mem_univ _, ⟨by linarith [hqt.2.1], by linarith [hqt.2.2]⟩⟩
  let T := F.restrOpen S (isOpen_univ.prod isOpen_Ioo)
  have hTs : T.source = S := inter_eq_right.mpr hSs
  have hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source := hF.mono inter_subset_left
  have hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target := hFi.mono inter_subset_left
  have hTheight (q : S1) (t : Real) (ht : t ∈ Ioo (a - ε) (b + ε)) :
      inner Real v (g (T (q, t))) = t :=
    hheight q t (hFs ▸ hSs (show (q, t) ∈ S from ⟨mem_univ q, ht⟩)).2
  let w := min (D.center - a) (b - E.center) / 4
  have hw : 0 < w := div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)
  have hwa : a + w < D.center := by
    dsimp [w]
    linarith [min_le_left (D.center - a) (b - E.center)]
  have hwb : E.center < b - w := by
    dsimp [w]
    linarith [min_le_right (D.center - a) (b - E.center)]
  have hprojD (t : Real) (ht : t ∈ Icc a (a + w)) :
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto (g (T (q, t)))) =
        D.planeMap '' sphere (0 : Hemisphere.Plane v) 1 := by
    let θ := (t - D.center) / D.scale
    have hθ : θ ∈ Icc (0 : Real) α := by
      refine ⟨div_nonneg_of_nonpos (by linarith [ht.2]) hDscale.le, ?_⟩
      apply (div_le_iff_of_neg hDscale).mpr
      have hh := ht.1
      change D.center + D.scale * α ≤ t at hh
      linarith
    have heq : D.center + D.scale * θ = t := by
      dsimp [θ]
      field_simp [D.scale_ne_zero]
      ring
    simpa only [T, OpenPartialHomeomorph.coe_restrOpen, heq] using hDcircle θ hθ
  have hprojE (t : Real) (ht : t ∈ Icc (b - w) b) :
      range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto (g (T (q, t)))) =
        E.planeMap '' sphere (0 : Hemisphere.Plane v) 1 := by
    let θ := (t - E.center) / E.scale
    have hθ : θ ∈ Icc (0 : Real) β := by
      refine ⟨div_nonneg (by linarith [ht.1]) hEscale.le, ?_⟩
      apply (div_le_iff₀ hEscale).mpr
      have hh := ht.2
      change t ≤ E.center + E.scale * β at hh
      linarith
    have heq : E.center + E.scale * θ = t := by
      dsimp [θ]
      field_simp [E.scale_ne_zero]
      ring
    simpa only [T, OpenPartialHomeomorph.coe_restrOpen, heq] using hEcircle θ hθ
  have haend : a ∈ Icc a (a + w) := ⟨le_rfl, by linarith⟩
  have hbend : b ∈ Icc (b - w) b := ⟨by linarith, le_rfl⟩
  obtain ⟨G, hG⟩ := exists_ambient_filling_of_capped_regular_annulus hg D.unit_v hε hw
    (hwa.trans (hDE.trans hwb)) T hTs hT hTi hTheight
    (fun t ht => (hprojD t ht).trans (hprojD a haend).symm)
    (fun t ht => (hprojE t ht).trans (hprojE b hbend).symm)
    D.planeMap E.planeMap (hprojD a haend).symm (hprojE b hbend).symm
    (-D.scale) E.scale (neg_pos.mpr hDscale) hEscale
  let N := g '' (T '' (univ ×ˢ Icc a b))
  have hN (y : E3) (hy : y ∈ N) : inner Real v y ∈ Icc a b := by
    obtain ⟨p, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩ := hy
    rw [hTheight q t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    exact ht
  obtain ⟨P, _, hP⟩ := exists_normalization_of_two_truncated_caps D E hDE hDscale hEscale
    hα hα1 hβ hβ1 N hN
  have hG' : G '' sphere (0 : E3) 1 = D.modelImageAt a ∪ N ∪ E.modelImageAt b := by
    simpa only [modelImageAt, neg_neg] using hG
  have hPrange : P '' range g = D.modelImageAt a ∪ N ∪ E.modelImageAt b := by
    rw [hrange']
    exact hP
  refine ⟨G.trans P.symm, ?_⟩
  apply P.injective.image_injective
  change P '' ((P.symm ∘ G) '' sphere (0 : E3) 1) = P '' range g
  rw [image_comp, image_image]
  simp only [P.apply_symm_apply, image_id']
  exact hG'.trans hPrange.symm

end SphereSurgeryCoreCap

namespace SphereSurgeryPath



theorem exists_ambient_filling_of_regular_core_of_cap_complement
    {v : E3} {f g : S2 → E3} (P : SphereSurgeryPath v f g)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hcaps : P.PreservesCaps) {B : Set Real}
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hregular : ∀ p ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      G '' sphere (0 : E3) 1 = range g := by
  obtain ⟨D, hD, E, hE, hDE, δ, hδ, F, hFs, hF, hFi, hheight, hCband⟩ :=
    P.exists_annular_core_of_regular hg hcaps L hpair hcore hregular
  have hends := SphereSurgeryCoreCap.cap_eq_end_of_annular_core L hpair hcore F hδ
    hFs hF hFi (h := fun p => inner Real v (g p)) hheight (fun _ _ => rfl)
    hCband D E hD hE rfl rfl
  obtain ⟨hDscale, hEscale⟩ := SphereSurgeryCoreCap.end_scales_of_annular_core
    L hpair hg.contMDiff.continuous hcore F hDE hδ hFs hheight hCband D E hD hE rfl rfl
  have htarget : P.core ⊆ F.target := by
    rw [hCband]
    rintro p ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    apply F.map_source
    rw [hFs]
    exact ⟨mem_univ _, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hboundary (A : SphereSurgeryCoreCap v g B) (hA : A ∈ L) :
      A.chart '' sphere (0 : E2) 1 ⊆ F.target := by
    intro p hp
    exact htarget ((SphereSurgeryCoreCap.core_inter_closed_disk L hpair hcore A hA).superset hp).1
  have hbase := SphereSurgeryCoreCap.range_eq_core_union_caps L hcore
  have hrange : range g = (D.parametrization '' closedBall 0 1) ∪
      (g '' (F '' (univ ×ˢ Icc D.center E.center))) ∪
        (E.parametrization '' closedBall 0 1) := by
    rw [hCband] at hbase
    rw [hbase]
    ext y
    constructor
    · rintro (hy | hy)
      · exact Or.inl (Or.inr hy)
      · obtain ⟨A, hA, hyA⟩ := mem_iUnion₂.mp hy
        rcases hends A hA with rfl | rfl
        · exact Or.inl (Or.inl hyA)
        · exact Or.inr hyA
    · rintro ((hyD | hy) | hyE)
      · exact Or.inr (mem_iUnion_of_mem D (mem_iUnion_of_mem hD hyD))
      · exact Or.inl hy
      · exact Or.inr (mem_iUnion_of_mem E (mem_iUnion_of_mem hE hyE))
  exact SphereSurgeryCoreCap.exists_ambient_filling_of_capped_annular_core D E hg hDE
    hDscale hEscale F hδ hFs hF hFi hheight (hboundary D hD) (hboundary E hE) hrange



theorem exists_ambient_filling_of_regular_core
    {v : E3} {f g : S2 → E3} (P : SphereSurgeryPath v f g)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hcaps : P.PreservesCaps)
    (hregular : ∀ p ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      G '' sphere (0 : E3) 1 = range g := by
  have hprotects : P.Protects ∅ := by
    clear hg hcaps hregular
    induction P <;> simp_all [Protects]
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hcaps hprotects
  exact P.exists_ambient_filling_of_regular_core_of_cap_complement
    hg hcaps L hpair hcore hregular

end SphereSurgeryPath

end Poincare.Manifold.Schoenflies
