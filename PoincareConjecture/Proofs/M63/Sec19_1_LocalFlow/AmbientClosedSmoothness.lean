import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactExtension
import PoincareConjecture.Proofs.M63.Mathlib.ClosedSpatialJetSmoothness
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem ambientCurve_contDiffOn_infty_Icc (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {L T : ℝ} (hL : 0 < L) (hT : 0 < T) (hTb : a + T < b)
    {q : ℝ → ℝ → W}
    (hper : ∀ t ∈ Icc 0 T, Function.Periodic (q t) L)
    (hspace : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (q t))
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (q z.1) z.2) (Icc 0 T ×ˢ univ))
    (hguard : ∀ t ∈ Icc 0 T, ∀ x, q t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0)
    (htime : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => q r x)
      (ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
          iteratedDeriv 2 (q t) x +
        ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
  let S : Set (ℝ × ℝ) := Icc 0 T ×ˢ univ
  let R (t x : ℝ) : W :=
    ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
      iteratedDeriv 2 (q t) x +
        ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)
  have hqc : ContinuousOn (Function.uncurry q) S := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def, S] using hjets 0
  have hqxc : ContinuousOn (fun z : ℝ × ℝ => deriv (q z.1) z.2) S := by
    simpa only [iteratedDeriv_one, S] using hjets 1
  have hparam : ContinuousOn (fun z : ℝ × ℝ =>
      ((a + z.1, q z.1 z.2), deriv (q z.1) z.2)) S :=
    ((continuousOn_const.add continuousOn_fst).prodMk hqc).prodMk hqxc
  have hmap : MapsTo (fun z : ℝ × ℝ =>
      ((a + z.1, q z.1 z.2), deriv (q z.1) z.2)) S
      {z : (ℝ × W) × W | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0} := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hguard z.1 hz.1 z.2⟩
  obtain ⟨hA, hB, _⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hAc := hA.continuousOn.comp (s := S) hparam hmap
  have hBc := hB.continuousOn.comp (s := S) hparam hmap
  have hRc : ContinuousOn (Function.uncurry R) S := (hAc.smul (hjets 2)).add hBc
  have hprimitive : ∀ t ∈ Icc 0 T, ∀ x,
      q t x = q 0 x + ∫ r in 0..t, R r x := by
    intro t ht x
    have hm : MapsTo (fun r : ℝ => (r, x)) (Icc 0 t) S :=
      fun r hr => ⟨⟨hr.1, hr.2.trans ht.2⟩, mem_univ _⟩
    have hslice : ContinuousOn (fun r : ℝ => (r, x)) (Icc 0 t) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hcontq := hqc.comp (s := Icc 0 t) hslice hm
    have hcontR := hRc.comp (s := Icc 0 t) hslice hm
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcontq
      (fun r hr => htime r ⟨hr.1, hr.2.trans_le ht.2⟩ x)
      (ContinuousOn.intervalIntegrable_of_Icc ht.1 hcontR)
    rw [hi]
    dsimp only [Function.comp_def, Function.uncurry_def]
    abel
  let j : ℝ × ℝ → W × W := fun z => (q z.1 z.2, deriv (q z.1) z.2)
  let K := j '' (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) L)
  have hjc : ContinuousOn j S := hqc.prodMk hqxc
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (hjc.mono (prod_mono_right (subset_univ _)))
  have hKsub : K ⊆ {z : W × W |
      z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} := by
    rintro z ⟨p, hp, rfl⟩
    exact hguard p.1 hp.1 p.2
  have hjmem (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) : j (t, x) ∈ K := by
    have hdper : Function.Periodic (deriv (q t)) L := by
      intro y
      have heq : (fun z => q t (z + L)) = q t := funext (hper t ht)
      rw [← deriv_comp_add_const, heq]
    have hjper : Function.Periodic (fun y => j (t, y)) L := by
      intro y
      exact Prod.ext (hper t ht y) (hdper y)
    obtain ⟨y, hy, hxy⟩ := hjper.exists_mem_Ico₀ hL x
    exact ⟨(t, y), ⟨ht, hy.1, hy.2.le⟩, hxy.symm⟩
  apply contDiffOn_infty_Icc_of_spatial_jets_and_finite_sources
    hT hspace hjets hprimitive
  intro m
  obtain ⟨C, hC, _hCc, O, _hO, hKO, _hOU, heq⟩ :=
    exists_ambientCurve_compact_extension F he hU hρ hK hKsub m hT.le
      (show T < b - a by linarith)
  let p : (ℝ × (W × (W × W))) → ℝ × (W × W) :=
    fun z => (z.1, (z.2.1, z.2.2.1))
  refine ⟨fun z => (1 - (C (p z)).1) • z.2.2.2 + (C (p z)).2, ?_, ?_⟩
  · have hp : ContDiff ℝ m p := by fun_prop
    have hCp := hC.comp hp
    exact ((contDiff_const.sub hCp.fst).smul contDiff_snd.snd.snd).add hCp.snd
  · intro t ht x
    have hCeq := heq (t, j (t, x)) (hKO ⟨ht, hjmem t ht x⟩) ht.1
    change R t x = (1 - (C (t, j (t, x))).1) • iteratedDeriv 2 (q t) x +
      (C (t, j (t, x))).2
    rw [hCeq]
    simp only [sub_sub_cancel, R, j]

end PoincareConjecture.M63
