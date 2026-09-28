import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClosedCurveFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactJetBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M63.Mathlib.ParabolicSpatialJetSmoothness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem c2ShrinkingCurve_smooth_of_embedded_spatial_jets
    (F : RicciFlow n M (Icc a b)) {tau s : ℝ} (hts : tau < s)
    {c : ℝ → ℝ → M} (hc : M63C2ShrinkingCurveOn F c (Icc tau s))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (hspace : ∀ t ∈ Ioo tau s, ContDiff ℝ ∞ (fun x => e (c x t)))
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (fun x => e (c x z.2)) z.1)
      (univ ×ˢ Ioo tau s)) :
    M63SmoothShrinkingCurveOn F c (Icc tau s) := by
  let q := fun t x => e (c x t)
  let Ω : Set (W × W) :=
    {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let D : Set ((ℝ × W) × W) :=
    {z | z.1.1 ∈ Ioo a b ∧ (z.1.2, z.2) ∈ Ω}
  let V : Set (ℝ × (W × (W × W))) :=
    {z | z.1 ∈ Ioo a b ∧ (z.2.1, z.2.2.1) ∈ Ω}
  let α : (ℝ × W) × W → ℝ :=
    fun z => ambientCurvePrincipal F ρ z.1.1 z.1.2 z.2
  let β : (ℝ × W) × W → W :=
    fun z => ambientCurveLower F e ρ z.1.1 z.1.2 z.2
  let P : ℝ × (W × (W × W)) → (ℝ × W) × W :=
    fun z => ((z.1, z.2.1), z.2.2.1)
  let direction : ℝ × (W × (W × W)) → (ℝ × W) × W :=
    fun z => ((0, z.2.2.1), z.2.2.2)
  let Φ : ℝ × (W × (W × W)) → W := fun z =>
    α (P z) • z.2.2.2 + β (P z) +
      (fderiv ℝ α (P z) (direction z) / 2) • z.2.2.1
  have hΩ : IsOpen Ω := isOpen_ambientCurveJetDomain F hU hρ
  have hD : IsOpen D := (isOpen_Ioo.preimage continuous_fst.fst).inter
    (hΩ.preimage (continuous_fst.snd.prodMk continuous_snd))
  have hV : IsOpen V := (isOpen_Ioo.preimage continuous_fst).inter
    (hΩ.preimage (continuous_snd.fst.prodMk continuous_snd.snd.fst))
  obtain ⟨hAraw, hBraw, _⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hα : ContDiffOn ℝ ∞ α D :=
    hAraw.mono (fun z hz => ⟨Ioo_subset_Icc_self hz.1, hz.2⟩)
  have hβ : ContDiffOn ℝ ∞ β D :=
    hBraw.mono (fun z hz => ⟨Ioo_subset_Icc_self hz.1, hz.2⟩)
  have hDα := hα.fderiv_of_isOpen hD (m := ∞) (by simp)
  have hP : ContDiff ℝ ∞ P := by fun_prop
  have hdir : ContDiff ℝ ∞ direction := by fun_prop
  have hPD : MapsTo P V D := fun _ hz => hz
  have hAc := hα.comp (s := V) hP.contDiffOn hPD
  have hBc := hβ.comp (s := V) hP.contDiffOn hPD
  have hDc := hDα.comp (s := V) hP.contDiffOn hPD
  have hfirst : ContDiffOn ℝ ∞
      (fun z : ℝ × (W × (W × W)) => z.2.2.1) V :=
    contDiff_snd.snd.fst.contDiffOn
  have hsecond : ContDiffOn ℝ ∞
      (fun z : ℝ × (W × (W × W)) => z.2.2.2) V :=
    contDiff_snd.snd.snd.contDiffOn
  have hΦ : ContDiffOn ℝ ∞ Φ V :=
    ((hAc.smul hsecond).add hBc).add
      (((hDc.clm_apply hdir.contDiffOn).div_const 2).smul hfirst)
  have hat : a ≤ tau := (hc.domain_subset ⟨le_rfl, hts.le⟩).1
  have hsb : s ≤ b := (hc.domain_subset ⟨hts.le, le_rfl⟩).2
  have htflow {t : ℝ} (ht : t ∈ Ioo tau s) : t ∈ Ioo a b :=
    ⟨hat.trans_lt ht.1, ht.2.trans_le hsb⟩
  have hdata := c2ShrinkingCurve_embedded_closed_data hc he
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hguard (t : ℝ) (ht : t ∈ Ioo tau s) (x : ℝ) :
      q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0 := by
    refine ⟨heU (mem_range_self _), ?_⟩
    have hd := (hdata.2.1 t (Ioo_subset_Icc_self ht) x).deriv
    change deriv (q t) x = _ at hd
    rw [hd]
    erw [hleft (c x t) (curveVelocity (n := n) (fun y => c y t) x)]
    exact hc.immersed t (Ioo_subset_Icc_self ht) x
  have hspatial (t : ℝ) (ht : t ∈ Ioo tau s) (x : ℝ) :
      deriv (fun y => α ((t, q t y), deriv (q t) y)) x =
        fderiv ℝ α ((t, q t x), deriv (q t) x)
          ((0, deriv (q t) x), iteratedDeriv 2 (q t) x) := by
    have hq := ((hspace t ht).differentiable (by simp) x).hasDerivAt
    have hq' : HasDerivAt (deriv (q t)) (iteratedDeriv 2 (q t) x) x := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        (((contDiff_infty_iff_deriv.mp (hspace t ht)).2).differentiable
          (by simp) x).hasDerivAt
    have hp : HasDerivAt (fun y => ((t, q t y), deriv (q t) y))
        ((0, deriv (q t) x), iteratedDeriv 2 (q t) x) x :=
      ((hasDerivAt_const x t).prodMk hq).prodMk hq'
    have hmem : ((t, q t x), deriv (q t) x) ∈ D := ⟨htflow ht, hguard t ht x⟩
    exact (((hα.contDiffAt (hD.mem_nhds hmem)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x hp).deriv
  have hcurv (t : ℝ) (ht : t ∈ Ioo tau s) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
        Φ (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x))) := by
    have hfixed (y : ℝ) : q t y = e (ρ (q t y)) := by
      dsimp only [q]
      rw [hρe]
    have heq := ambientCurve_embeddedCurvature_eq F he hU heU hρ hρe t
      ((hspace t ht).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hguard t ht) hfixed x
    have hslice : (fun y => ρ (q t y)) = fun y => c y t :=
      funext fun y => hρe (c y t)
    have hpush := congrArg (fun gamma : ℝ → M =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x)
        (m62CurvatureVector F (fun y (_ : ℝ) => gamma y) t x) : W)) hslice
    change mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (q t x))
      (m62CurvatureVector F (fun y (_ : ℝ) => ρ (q t y)) t x) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) at hpush
    rw [hpush] at heq
    change mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
      α ((t, q t x), deriv (q t) x) • deriv (deriv (q t)) x +
        β ((t, q t x), deriv (q t) x) +
          (deriv (fun y => α ((t, q t y), deriv (q t) y)) x / 2) • deriv (q t) x at heq
    rw [hspatial t ht x] at heq
    simpa only [Φ, P, direction, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero] using heq
  have htime (t : ℝ) (ht : t ∈ Ioo tau s) (x : ℝ) :
      HasDerivAt (fun r => q r x)
        (Φ (t, (q t x, (deriv (q t) x, iteratedDeriv 2 (q t) x)))) t := by
    have hd := (c2ShrinkingCurve_embedded_interior_equation hc he).2 t
      (by simpa only [interior_Icc] using ht) x
    exact hd.congr_deriv (hcurv t ht x)
  have hjet (k : ℕ) : ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (q z.1) z.2) (Ioo tau s ×ˢ univ) :=
    (hjets k).comp continuous_swap.continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
  have hq := contDiffOn_infty_of_spatial_jets_and_equation hV hΦ hspace hjet
    (fun t ht x => ⟨htflow ht, hguard t ht x⟩) htime
  have hswap : ContDiff ℝ ∞ (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hq' := hq.comp (s := univ ×ˢ Ioo tau s) hswap.contDiffOn
    (fun z hz => ⟨hz.2, hz.1⟩)
  have hm := hρ.comp hq'.contMDiffOn (fun z _hz => heU (mem_range_self (c z.1 z.2)))
  refine ⟨hc, ?_⟩
  rw [interior_Icc]
  exact hm.congr (fun z _hz => (hρe (c z.1 z.2)).symm)

end PoincareConjecture.M63
