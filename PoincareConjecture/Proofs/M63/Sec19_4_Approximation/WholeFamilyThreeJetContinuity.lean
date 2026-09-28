import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FamilyThreeJetTimeModulus
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.VariableTimeEmbeddedJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousDependenceAngularJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalCurveTheory
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {Z : Type u} [TopologicalSpace Z] [CompactSpace Z]
  {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem continuous_family_embedded_threeJets_of_curvature_bound
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U)
    (hrhoe : ∀ p, rho (e p) = p)
    (c : Z → ℝ → ℝ → M) (hc : ∀ z, M62ShrinkingCurve F (c z))
    (hzero : Continuous (fun z : Z × ℝ => e (c z.1 z.2 a)))
    (hfirst : Continuous (fun z : Z × ℝ =>
      deriv (fun y => e (c z.1 y a)) z.2))
    (hsecond : Continuous (fun z : Z × ℝ =>
      deriv (deriv (fun y => e (c z.1 y a))) z.2))
    {R nu0 V0 B0 : ℝ}
    (hR : 0 ≤ R) (hnu0 : 0 < nu0) (hV0 : 0 ≤ V0) (hB0 : 0 ≤ B0)
    (hinitial : ∀ z x, nu0 ≤ curveSpeed F (c z) a x ∧
      curveSpeed F (c z) a x ≤ V0)
    (hgradient : ∀ z x, |deriv (curveSpeed F (c z) a) x| ≤ B0)
    (hcurvature : ∀ z t, t ∈ Ioo a b → ∀ x,
      m62CurvatureSquared F (c z) t x ≤ R) :
    Continuous (fun z : (Z × ℝ) × Icc a b => e (c z.1.1 z.1.2 z.2)) ∧
    Continuous (fun z : (Z × ℝ) × Icc a b =>
      deriv (fun y => e (c z.1.1 y z.2)) z.1.2) ∧
    Continuous (fun z : (Z × ℝ) × Icc a b =>
      deriv (deriv (fun y => e (c z.1.1 y z.2))) z.1.2) := by
  classical
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  let Y := (W × W) × W
  let J : (Z × ℝ) × ℝ → Y := fun w =>
    ((e (c w.1.1 w.1.2 w.2), deriv (fun y => e (c w.1.1 y w.2)) w.1.2),
      deriv (deriv (fun y => e (c w.1.1 y w.2))) w.1.2)
  have hstep (T : ℝ) (haT : a ≤ T) (hTb : T < b)
      (hJT : Continuous (fun z : Z × ℝ => J (z, T))) :
      ∃ S : ℝ, T < S ∧ S ≤ b ∧ ContinuousOn J (univ ×ˢ Icc T S) := by
    let FT := m63RestrictClosedFlow F T b (Icc_subset_Icc haT le_rfl) hTb
    have hct (z : Z) : M62ShrinkingCurve FT (c z) :=
      m63SmoothRestriction (m63SmoothClosed_iff_m62.mpr (hc z)) T b
        (Icc_subset_Icc haT le_rfl) hTb
    let LT := localCurveTheory_of_compact FT hcompact
    have hg0 : Continuous (fun z : Z × ℝ => e (c z.1 z.2 T)) := hJT.fst.fst
    have hg1 : Continuous (fun z : Z × ℝ =>
        deriv (fun y => e (c z.1 y T)) z.2) := hJT.fst.snd
    have hg2 : Continuous (fun z : Z × ℝ =>
        deriv (deriv (fun y => e (c z.1 y T))) z.2) := hJT.snd
    obtain ⟨hgamma, hangular1, hangular2⟩ :=
      continuous_angular_jets_of_embedded_jets FT (fun _ : Z => T) continuous_const
        (fun _ => ⟨le_rfl, hTb.le⟩) (fun z x => c z x T)
        (fun z => (hct z).spatial_regular T ⟨le_rfl, hTb.le⟩)
        he hU heU hrho hrhoe hg0 hg1 hg2
    obtain ⟨S, hTS, hSb, d, hd, hd0, _hdi, hdcont, hd1, hd2⟩ :=
      LT.continuous_dependence Z (fun z x => c z x T) hgamma hangular1 hangular2
        (fun z => (hct z).periodic T ⟨le_rfl, hTb.le⟩)
        (fun z => (hct z).spatial_regular T ⟨le_rfl, hTb.le⟩)
        (fun z x => (hct z).immersed T ⟨le_rfl, hTb.le⟩ x)
    have hmatch (z : Z) : ∀ t ∈ Icc T S, ∀ x, c z x t = d z x t :=
      LT.unique_closed S hTS hSb (c z) (d z)
        (c2_restrict (m63C2_of_m62 (hct z)) (Icc_subset_Icc_right hSb))
        (hd z) (fun x => (hd0 z x).symm)
    let reorder : (Z × Icc T S) × ℝ → (Z × ℝ) × Icc T S :=
      fun w => ((w.1.1, w.2), w.1.2)
    have hreorder : Continuous reorder := by fun_prop
    obtain ⟨_hspace, hz, hp, hq⟩ :=
      continuous_embedded_jets_of_angular_jets FT
        (fun z : Z × Icc T S => (z.2 : ℝ))
        (continuous_subtype_val.comp continuous_snd)
        (fun z => ⟨z.2.2.1, z.2.2.2.trans hSb⟩)
        (fun z x => d z.1 x z.2) (hdcont.comp hreorder)
        (hd1.comp hreorder) (hd2.comp hreorder)
        (fun z => (hd z.1).spatial_regular z.2 z.2.2) he hU heU hrho hrhoe
    let inverseReorder : (Z × ℝ) × Icc T S → (Z × Icc T S) × ℝ :=
      fun w => ((w.1.1, w.2), w.1.2)
    have hinverseReorder : Continuous inverseReorder := by fun_prop
    have hdjets : Continuous (fun w : (Z × ℝ) × Icc T S =>
        ((e (d w.1.1 w.1.2 w.2), deriv (fun y => e (d w.1.1 y w.2)) w.1.2),
          deriv (deriv (fun y => e (d w.1.1 y w.2))) w.1.2)) :=
      ((hz.prodMk hp).prodMk hq).comp hinverseReorder
    have hretained : Continuous (fun w : (Z × ℝ) × Icc T S => J (w.1, w.2)) := by
      apply hdjets.congr
      intro w
      exact congrArg (fun f : ℝ → W => ((f w.1.2, deriv f w.1.2),
        deriv (deriv f) w.1.2))
        (funext (fun x => congrArg e (hmatch w.1.1 w.2 w.2.2 x).symm))
    refine ⟨S, hTS, hSb, ?_⟩
    rw [continuousOn_iff_continuous_domRestrict]
    let inclusion : (univ ×ˢ Icc T S : Set ((Z × ℝ) × ℝ)) →
        (Z × ℝ) × Icc T S := fun w => (w.1.1, ⟨w.1.2, w.2.2⟩)
    have hinclusion : Continuous inclusion := by fun_prop
    exact hretained.comp hinclusion
  have hJ0 : Continuous (fun z : Z × ℝ => J (z, a)) :=
    (hzero.prodMk hfirst).prodMk hsecond
  obtain ⟨T0, haT0, hT0b, hT0⟩ := hstep a le_rfl hab hJ0
  let E : Set ℝ := {T | a ≤ T ∧ T ≤ b ∧ ContinuousOn J (univ ×ˢ Icc a T)}
  have hT0mem : T0 ∈ E := ⟨haT0.le, hT0b, hT0⟩
  have hE : E.Nonempty := ⟨T0, hT0mem⟩
  have hBdd : BddAbove E := ⟨b, fun T hT => hT.2.1⟩
  let Tstar := sSup E
  have haStar : a < Tstar := haT0.trans_le (le_csSup hBdd hT0mem)
  have hStarb : Tstar ≤ b := csSup_le hE (fun T hT => hT.2.1)
  have hbelow (k : ℝ) (hk : k < Tstar) :
      ContinuousOn J (univ ×ˢ Icc a k) := by
    obtain ⟨T, hT, hkT⟩ := exists_lt_of_lt_csSup hE hk
    exact hT.2.2.mono (prod_mono Subset.rfl (Icc_subset_Icc_right hkT.le))
  obtain ⟨tau, hat, htauStar⟩ := exists_between haStar
  have htaub : tau < b := htauStar.trans_le hStarb
  let X := (Z × ℝ) × Icc a Tstar
  let clamp : ℝ → X → Y := fun k w => J (w.1, min (w.2 : ℝ) k)
  have hnear : ∀ᶠ k : ℝ in 𝓝[<] Tstar, tau < k ∧ k < Tstar := by
    have hlow : ∀ᶠ k : ℝ in 𝓝[<] Tstar, tau < k :=
      (eventually_gt_nhds htauStar).filter_mono nhdsWithin_le_nhds
    exact hlow.and self_mem_nhdsWithin
  have hclamp : ∀ᶠ k : ℝ in 𝓝[<] Tstar, Continuous (clamp k) := by
    filter_upwards [hnear] with k hk
    have hmap : Continuous (fun w : X => (w.1, min (w.2 : ℝ) k)) := by
      change Continuous (fun w : (Z × ℝ) × Icc a Tstar => (w.1, min (w.2 : ℝ) k))
      exact continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).min continuous_const)
    exact (hbelow k hk.2).comp_continuous hmap
      (fun w => ⟨mem_univ _, le_min w.2.2.1 (hat.trans hk.1).le, min_le_right _ _⟩)
  have hlimit : TendstoUniformly clamp (fun w : X => J (w.1, w.2))
      (𝓝[<] Tstar) := by
    rw [Metric.tendstoUniformly_iff]
    intro epsilon hepsilon
    obtain ⟨eta, heta, hmod⟩ := exists_uniform_embedded_threeJet_time_modulus
      F hcompact he hU heU hrho hrhoe hat htaub hR hnu0 hV0 hB0 epsilon hepsilon
    have hclose : ∀ᶠ k : ℝ in 𝓝[<] Tstar, Tstar - eta < k :=
      (eventually_gt_nhds (sub_lt_self Tstar heta)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnear, hclose] with k hk hketa w
    by_cases htk : (w.2 : ℝ) ≤ k
    · simpa only [clamp, min_eq_left htk, dist_self] using hepsilon
    · have hkt : k < (w.2 : ℝ) := lt_of_not_ge htk
      have ht : (w.2 : ℝ) ∈ Icc tau b :=
        ⟨hk.1.le.trans hkt.le, w.2.2.2.trans hStarb⟩
      have hkI : k ∈ Icc tau b := ⟨hk.1.le, hk.2.le.trans hStarb⟩
      have hdist : |(w.2 : ℝ) - k| < eta := by
        rw [abs_of_nonneg (sub_nonneg.mpr hkt.le)]
        linarith only [w.2.2.2, hketa]
      have h := hmod (c w.1.1) (hc w.1.1) (hinitial w.1.1) (hgradient w.1.1)
        (hcurvature w.1.1) w.2 ht k hkI hdist w.1.2
      change dist (J (w.1, (w.2 : ℝ))) (J (w.1, min (w.2 : ℝ) k)) < epsilon
      rw [min_eq_right hkt.le]
      change max (max ‖e (c w.1.1 w.1.2 w.2) - e (c w.1.1 w.1.2 k)‖
        ‖deriv (fun y => e (c w.1.1 y w.2)) w.1.2 -
          deriv (fun y => e (c w.1.1 y k)) w.1.2‖)
        ‖deriv (deriv (fun y => e (c w.1.1 y w.2))) w.1.2 -
          deriv (deriv (fun y => e (c w.1.1 y k))) w.1.2‖ < epsilon
      exact max_lt_iff.mpr ⟨max_lt_iff.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  have hprefix : ContinuousOn J (univ ×ˢ Icc a Tstar) := by
    have hclosed := hlimit.continuous hclamp.frequently
    rw [continuousOn_iff_continuous_domRestrict]
    let inclusion : (univ ×ˢ Icc a Tstar : Set ((Z × ℝ) × ℝ)) → X :=
      fun w => (w.1.1, ⟨w.1.2, w.2.2⟩)
    have hinclusion : Continuous inclusion := by fun_prop
    exact hclosed.comp hinclusion
  have hStar : Tstar = b := by
    apply le_antisymm hStarb
    by_contra! hTb
    have hJT : Continuous (fun z : Z × ℝ => J (z, Tstar)) :=
      hprefix.comp_continuous (continuous_id.prodMk continuous_const)
        (fun _ => ⟨mem_univ _, haStar.le, le_rfl⟩)
    obtain ⟨S, hStarS, hSb, hright⟩ := hstep Tstar haStar.le hTb hJT
    have hwhole : ContinuousOn J (univ ×ˢ Icc a S) := by
      apply (hprefix.union_of_isClosed hright
        (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)).mono
      intro w hw
      by_cases htime : w.2 ≤ Tstar
      · exact Or.inl ⟨hw.1, hw.2.1, htime⟩
      · exact Or.inr ⟨hw.1, (lt_of_not_ge htime).le, hw.2.2⟩
    have hSmem : S ∈ E := ⟨haStar.le.trans hStarS.le, hSb, hwhole⟩
    exact (not_lt_of_ge (le_csSup hBdd hSmem)) hStarS
  rw [hStar] at hprefix
  have hfinal : Continuous (fun w : (Z × ℝ) × Icc a b => J (w.1, w.2)) :=
    hprefix.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun w => ⟨mem_univ _, w.2.2⟩)
  exact ⟨hfinal.fst.fst, hfinal.fst.snd, hfinal.snd⟩

end PoincareConjecture.M63
