import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelSpatialSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddedNormalSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialArclengthGauge
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding











set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem exists_fixed_smooth_relabeling [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) (hi : M63IntrinsicRegularityOn F c J)
    {tau s : ℝ} (hat : a < tau) (hts : tau < s) (hslab : Icc tau s ⊆ J) :
    ∃ (phi : ℝ → ℝ) (d : ℝ → ℝ → M),
      ContDiff ℝ 2 phi ∧ Function.Bijective phi ∧
      (∀ x, 0 < deriv phi x) ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      M63SmoothShrinkingCurveOn F d (Icc tau s) ∧
      (∀ t ∈ Icc tau s, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => d x t)) ∧
      ∀ t ∈ Icc tau s, ∀ x, c x t = d (phi x) t := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 tau⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  have htau : tau ∈ J := hslab ⟨le_rfl, hts.le⟩
  obtain ⟨_hell, phi, _hformula, hphi, hpsi, _hzero, hpos, hpsipos,
    hshift, hpsishift, _hperiod, _hregular, _himm, hanchor, _hprincipal⟩ :=
    exists_c2_constant_speed_relabeling F (fun x => c x tau) tau
      (hc.periodic tau htau) (hc.spatial_regular tau htau) (hc.immersed tau htau)
  let d := fun x t => c (phi.symm x) t
  change ∀ x, curveSpeed F d tau x = _ at hanchor
  obtain ⟨_Q, _hQvalue, _hQ, hslice, hjets⟩ :=
    fixedLabel_embedded_path_smooth_of_constant_speed F hc hi hat hts hslab
      hpsi hpsipos hpsishift hanchor he hU heU hρ hρe
  have hd : M63C2ShrinkingCurveOn F d (Icc tau s) :=
    c2_restrict (c2ShrinkingCurve_fixedLabel_comp F hc hpsi hpsipos hpsishift) hslab
  have hsmooth : M63SmoothShrinkingCurveOn F d (Icc tau s) :=
    c2ShrinkingCurve_smooth_of_embedded_spatial_jets F hts hd he hU heU hρ hρe
      (fun t ht => (he.comp (hslice t (Ioo_subset_Icc_self ht))).contDiff)
      (fun k => (hjets k).mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
  refine ⟨phi, d, hphi, phi.bijective, hpos, hshift, hsmooth, hslice, ?_⟩
  intro t _ht x
  change c x t = c (phi.symm (phi x)) t
  rw [phi.symm_apply_apply]

end PoincareConjecture.M63
