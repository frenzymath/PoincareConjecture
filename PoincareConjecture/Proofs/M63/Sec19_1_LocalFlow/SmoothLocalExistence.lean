import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientNormalFlow
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClassicalExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClosedSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothUnitSpeedParameter
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothIntrinsicRestriction
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicLabelFlow
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





theorem exists_smooth_local_curve_of_retraction (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : ℝ → M) (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    ∃ T : ℝ, a < T ∧ T < b ∧ ∃ c : ℝ → ℝ → M,
      M63SmoothShrinkingCurveOn F c (Icc a T) ∧
      (∀ x, c x a = gamma x) ∧ M63IntrinsicRegularityOn F c (Icc a T) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
        (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a T) := by
  classical
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  let L := ∫ x in (0 : ℝ)..curvePeriod, curveSpeed F (fun y _ => gamma y) a x
  obtain ⟨hL, σ, _hσformula, hσ, _hσinv, _hσzero, hσpos, _hσinvpos, hσshift,
      _hσinvshift, hper0, hgamma0, himm0, _hunit0, hprincipal0, _hrecover⟩ :=
    exists_smooth_unit_speed_parameter F gamma a hperiod hgamma himm
  let gamma0 := fun y => gamma (σ.symm y)
  let fReal := fun y => e (gamma0 y)
  have hfReal : ContDiff ℝ ∞ fReal := (he.comp hgamma0).contDiff
  have hfper : Function.Periodic fReal L := hper0.comp e
  let f : C(AddCircle L, W) := ⟨hfper.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
      hfReal.continuous⟩
  have hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle L)) := hfReal
  have hρf : (fun y : ℝ => ρ (f (y : AddCircle L))) = gamma0 :=
    funext fun y => hρe (gamma0 y)
  have hproject (x : ℝ) :
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f (x : AddCircle L))
          (deriv (fun y : ℝ => f (y : AddCircle L)) x) =
        curveVelocity (n := n) gamma0 x := by
    have hv : curveVelocity (n := n) (fun y : ℝ => ρ (f (y : AddCircle L))) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f (x : AddCircle L))
          (deriv (fun y : ℝ => f (y : AddCircle L)) x) := by
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ fun y : ℝ => f (y : AddCircle L)) x) 1 = _
      erw [mfderiv_comp x
        ((hρ.contMDiffAt (hU.mem_nhds (heU (mem_range_self _)))).mdifferentiableAt (by simp))
        ((hf.contMDiff x).mdifferentiableAt (by simp)),
        ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
      rfl
    rw [hρf] at hv
    exact hv.symm
  have hfguard (x : ℝ) : f (x : AddCircle L) ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f (x : AddCircle L))
        (deriv (fun y : ℝ => f (y : AddCircle L)) x) ≠ 0 := by
    refine ⟨heU (mem_range_self _), ?_⟩
    rw [hproject]
    exact himm0 x
  have hfunit (x : ℝ) : ambientCurvePrincipal F ρ a (f (x : AddCircle L))
      (deriv (fun y : ℝ => f (y : AddCircle L)) x) = 1 := by
    unfold ambientCurvePrincipal
    rw [hproject]
    change ((F.metric a).inner (ρ (e (gamma0 x)))
      (curveVelocity gamma0 x) (curveVelocity gamma0 x))⁻¹ = 1
    rw [hρe, ← M62.speed_sq F (fun y _ => gamma0 y) a x]
    exact hprincipal0 x
  have hffixed (x : ℝ) : f (x : AddCircle L) = e (ρ (f (x : AddCircle L))) := by
    change e (gamma0 x) = e (ρ (e (gamma0 x)))
    rw [hρe]
  obtain ⟨T0, hT0, hTcap, _hT1, q, _hqc, hqper, hqzero, hqspace, hqjets,
      hqguard, hqtime, _hqC1, hqfixed⟩ :=
    exists_ambient_classical_curve_of_unit_initial F he hU heU hρ hρe hL f hf
      hfguard hfunit hffixed (Tcap := (b - a) / 2) (by linarith) (by linarith)
  have hT0b : a + T0 < b := by linarith
  have hjets (k : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (q z.1) z.2) (Icc 0 T0 ×ˢ univ) := by
    obtain ⟨J, hJ⟩ := hqjets k
    have hcont : Continuous (fun z : ℝ × ℝ =>
        J (projIcc 0 T0 hT0.le z.1) (z.2 : AddCircle L)) :=
      continuous_eval.comp ((J.continuous.comp
        (continuous_projIcc.comp continuous_fst)).prodMk
          ((AddCircle.continuous_mk' L).comp continuous_snd))
    apply hcont.continuousOn.congr
    intro z hz
    change iteratedDeriv k (q z.1) z.2 = J (projIcc 0 T0 hT0.le z.1) (z.2 : AddCircle L)
    rw [projIcc_of_mem hT0.le hz.1]
    exact hJ ⟨z.1, hz.1⟩ z.2
  have hqjoint := ambientCurve_contDiffOn_infty_Icc F he hU hρ hL hT0 hT0b
    (fun t _ => hqper t) (fun t _ => hqspace t) hjets hqguard hqtime
  let A := fun t y => ambientCurvePrincipal F ρ (a + t) (q t y) (deriv (q t) y)
  let w := fun t y => deriv (A t) y / 2
  obtain ⟨hw, hwper⟩ := ambientCurve_labelVelocity_regular F hU hρ hT0 hT0b.le
    hqjoint (fun t _ => hqper t) hqguard
  let v := fun t y => if t ∈ Icc 0 T0 then w t y else 0
  have hvper (t : ℝ) : Function.Periodic (v t) L := by
    intro y
    dsimp only [v]
    split_ifs with ht
    · exact hwper t ht y
    · rfl
  have hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Ico 0 T0 ×ˢ univ) := by
    apply (hw.mono (prod_mono Ico_subset_Icc_self Subset.rfl)).congr
    intro z hz
    exact if_pos ⟨hz.1.1, hz.1.2.le⟩
  obtain ⟨δ, hδ, hδT, _hδ1, ψ, hψzero, hψper, hψjoint, hψode, hψpos, _hψbij⟩ :=
    exists_smooth_periodic_label_flow hL hT0 v hvper hv
  have hδT0 : δ < T0 := by linarith
  have hψactual (t : ℝ) (ht : t ∈ Icc 0 δ) (y : ℝ) :
      HasDerivWithinAt (fun s => ψ s y)
        (deriv (A t) (ψ t y) / 2) (Icc 0 δ) t := by
    have hm : t ∈ Icc 0 T0 := ⟨ht.1, ht.2.trans hδT0.le⟩
    simpa only [v, if_pos hm] using hψode t ht y
  have htime (t : ℝ) (ht : t ∈ Ioo 0 T0) (y : ℝ) :
      HasDerivAt (fun s => q s y)
        (ambientCurvePrincipal F ρ (a + t) (q t y) (deriv (q t) y) •
            deriv (deriv (q t)) y +
          ambientCurveLower F e ρ (a + t) (q t y) (deriv (q t) y)) t := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hqtime t ht y
  obtain ⟨hc, hcinitial, hcjoint⟩ := ambientCurve_normal_solution_of_labels F he hU heU hρ hρe
    hT0 hT0b.le hqjoint (fun t _ => hqper t) hqguard hqfixed htime
    hσ hσpos hσshift hδ hδT0 hψzero hψjoint hψper hψpos hψactual
  let c := fun x t => ρ (q (t - a) (ψ (t - a) (σ x)))
  have hshort : Icc a (a + δ / 2) ⊆ Icc a (a + δ) :=
    fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  refine ⟨a + δ / 2, by linarith, by linarith, c,
    ⟨c2_restrict hc.1 hshort, hc.2.mono (prod_mono Subset.rfl (interior_mono hshort))⟩,
    ?_, ?_, hcjoint.mono (prod_mono Subset.rfl hshort)⟩
  · intro x
    calc c x a = ρ (q 0 (σ x)) := hcinitial x
         _ = gamma x := ?_
    rw [hqzero]
    change ρ (e (gamma (σ.symm (σ x)))) = gamma x
    rw [hρe, σ.symm_apply_apply]
  · exact intrinsic_regularity_on_shorter_smooth_slab F c
      (by linarith) (by linarith) (by linarith) hc




theorem exists_smooth_local_curve [CompactSpace M] (F : RicciFlow n M (Icc a b))
    (gamma : ℝ → M) (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    ∃ T : ℝ, a < T ∧ T < b ∧ ∃ c : ℝ → ℝ → M,
      M63SmoothShrinkingCurveOn F c (Icc a T) ∧
      (∀ x, c x a = gamma x) ∧ M63IntrinsicRegularityOn F c (Icc a T) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
        (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a T) := by
  let : Nonempty M := ⟨gamma 0⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  exact exists_smooth_local_curve_of_retraction F he hU heU hρ hρe gamma hperiod hgamma himm

end PoincareConjecture.M63
