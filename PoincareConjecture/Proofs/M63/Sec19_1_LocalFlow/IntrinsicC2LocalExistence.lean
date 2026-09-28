import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicC2UnitSpeedExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UnitSpeedInitialPeriod
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelC2Transport
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem exists_intrinsic_c2_local_curve_of_retraction
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : ℝ → M) (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    ∃ T : ℝ, a < T ∧ T < b ∧ ∃ c : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Icc a T) ∧
      (∀ x, c x a = gamma x) ∧ M63IntrinsicRegularityOn F c (Icc a T) := by
  let L := ∫ x in (0 : ℝ)..curvePeriod, curveSpeed F (fun y _ => gamma y) a x
  obtain ⟨hL, σ, _hσformula, hσ, _hσinv, _hσzero, hσpos, _hσinvpos, hσshift,
      _hσinvshift, hper0, hgamma0, himm0, hunit0, _hprincipal0, _hrecover⟩ :=
    exists_c2_unit_speed_parameter F gamma a hperiod hgamma himm
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos hL Real.two_pi_pos
  obtain ⟨S, haS, hSb, d, hd, hd0, hi⟩ :=
    exists_intrinsic_c2_local_curve_of_unit_initial F hcompact
      he hU heU hρ hρe hL hper0 hgamma0 himm0 hunit0
  let phi : ℝ → ℝ := fun x => σ x / κ
  have hphi : ContDiff ℝ 2 phi := hσ.div_const κ
  have hphipos (x : ℝ) : 0 < deriv phi x := by
    have hdphi := ((hσ.differentiable (by norm_num) x).hasDerivAt).div_const κ
    rw [hdphi.deriv]
    exact div_pos (hσpos x) hκ
  have hphishift (x : ℝ) : phi (x + curvePeriod) = phi x + curvePeriod := by
    change σ (x + curvePeriod) / κ = σ x / κ + curvePeriod
    rw [hσshift, add_div]
    congr 1
    dsimp only [κ, L]
    field_simp [hL.ne', Real.two_pi_pos.ne']
  have hcancel (x : ℝ) : κ * phi x = σ x := by
    dsimp only [phi]
    field_simp [hκ.ne']
  let T := (a + S) / 2
  have haT : a < T := by dsimp only [T]; linarith only [haS]
  have hTS : T < S := by dsimp only [T]; linarith only [haS]
  have hsub : Icc a T ⊆ Icc a S := Icc_subset_Icc_right hTS.le
  let c := fun x t => d (phi x) t
  have hc : M63C2ShrinkingCurveOn F c (Icc a T) :=
    c2_restrict (c2ShrinkingCurve_fixedLabel_comp F hd hphi hphipos hphishift) hsub
  have hslice (i : ℕ) (t : ℝ) (ht : t ∈ Ioo a S) :
      ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun y => (⟨d y t, m63CurvatureJet F d i t y⟩ : TangentBundle (𝓡 n) M)) := by
    intro x
    have hm : (x, t) ∈ univ ×ˢ interior (Icc a S) :=
      ⟨mem_univ _, by simpa only [interior_Icc] using ht⟩
    have hiat := ((hi.interior_jets i) (x, t) hm).contMDiffAt
      ((isOpen_univ.prod isOpen_interior).mem_nhds hm)
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1 (fun y : ℝ => (y, t)) x :=
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
    exact hiat.comp x hline
  have hjet (i : ℕ) (t : ℝ) (ht : t ∈ Ioo a S) (x : ℝ) :
      m63CurvatureJet F c i t x = m63CurvatureJet F d i t (phi x) :=
    curvatureJet_comp F d ((hd.spatial_regular t (Ioo_subset_Icc_self ht)).mdifferentiable
      (by norm_num)) (hphi.differentiable (by norm_num)) hphipos
      (fun y => (unitTangent_contMDiff_of_c2 F d
        (hd.spatial_regular t (Ioo_subset_Icc_self ht))
        (hd.immersed t (Ioo_subset_Icc_self ht)) (phi y)).mdifferentiableAt (by norm_num))
      (fun k y => (hslice k t ht (phi y)).mdifferentiableAt (by norm_num)) i x
  let B : ℝ × ℝ → ℝ × ℝ := fun z => (phi z.1, z.2)
  have hB : ContDiff ℝ 1 B :=
    ((hphi.of_le (by norm_num)).comp contDiff_fst).prodMk contDiff_snd
  have hnew (i : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a S) := by
    have hold := hi.interior_jets i
    rw [interior_Icc] at hold
    have hcomp := hold.comp (s := univ ×ˢ Ioo a S) (f := B)
      hB.contMDiff.contMDiffOn (fun _ hz => ⟨mem_univ _, hz.2⟩)
    apply hcomp.congr
    intro z hz
    change (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M) =
      (⟨c z.1 z.2, m63CurvatureJet F d i z.2 (phi z.1)⟩ : TangentBundle (𝓡 n) M)
    rw [hjet i z.2 hz.2 z.1]
  refine ⟨T, haT, hTS.trans hSb, c, hc, ?_, ?_⟩
  · intro x
    change d (phi x) a = gamma x
    rw [hd0]
    change gamma (σ.symm (κ * phi x)) = gamma x
    rw [hcancel, σ.symm_apply_apply]
  · refine { interior_jets := ?_, closed_positive_jets := ?_ }
    · intro i
      rw [interior_Icc]
      exact (hnew i).mono (prod_mono Subset.rfl
        (fun _ ht => ⟨ht.1, ht.2.trans hTS⟩))
    · intro tau s hat _hts hslab i
      exact (hnew i).continuousOn.mono (prod_mono Subset.rfl
        (fun t ht => ⟨hat.trans_le ht.1, (hslab ht).2.trans_lt hTS⟩))




theorem exists_intrinsic_c2_local_curve [CompactSpace M]
    (F : RicciFlow n M (Icc a b)) (gamma : ℝ → M)
    (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    ∃ T : ℝ, a < T ∧ T < b ∧ ∃ c : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Icc a T) ∧
      (∀ x, c x a = gamma x) ∧ M63IntrinsicRegularityOn F c (Icc a T) := by
  let : Nonempty M := ⟨gamma 0⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  exact exists_intrinsic_c2_local_curve_of_retraction F isCompact_univ
    he hU heU hρ hρe gamma hperiod hgamma himm

end PoincareConjecture.M63
