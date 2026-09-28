import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactJetBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem ambientCurve_preserves_retraction (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {L T : ℝ} (hL : 0 < L) (hT : 0 < T) (hTb : a + T ≤ b)
    (q : ℝ → ℝ → W)
    (hqc : ContinuousOn (Function.uncurry q) (Icc (0 : ℝ) T ×ˢ univ))
    (hqxc : ContinuousOn (fun z : ℝ × ℝ => deriv (q z.1) z.2)
      (Icc (0 : ℝ) T ×ˢ univ))
    (hper : ∀ t ∈ Icc (0 : ℝ) T, Function.Periodic (q t) L)
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (q t))
    (hguard : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0)
    (htime : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => q s x)
      (ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
          iteratedDeriv 2 (q t) x +
        ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)) t)
    (hinit : ∀ x, q 0 x = e (ρ (q 0 x))) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, q t x = e (ρ (q t x)) := by
  let r : W → W := e ∘ ρ
  let j : ℝ × ℝ → W × W := fun z => (q z.1 z.2, deriv (q z.1) z.2)
  let K0 := j '' (Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) L)
  let P : W × W → W × W := fun z => (r z.1, fderiv ℝ r z.1 z.2)
  let K := K0 ∪ P '' K0
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  obtain ⟨hr, hDr, hleft⟩ := smooth_retraction_differentials he hU heU hρ hρe
  have hjc : ContinuousOn j (Icc (0 : ℝ) T ×ˢ univ) := hqc.prodMk hqxc
  have hK0 : IsCompact K0 :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (hjc.mono (prod_mono_right (subset_univ _)))
  have hK0sub : K0 ⊆ Ω := by
    rintro z ⟨p, hp, rfl⟩
    exact hguard p.1 hp.1 p.2
  have hjmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℝ) : j (t, x) ∈ K0 := by
    have hdper : Function.Periodic (deriv (q t)) L := by
      intro y
      have heq : (fun z => q t (z + L)) = q t := funext (hper t ht)
      rw [← deriv_comp_add_const, heq]
    have hjper : Function.Periodic (fun y => j (t, y)) L := by
      intro y
      exact Prod.ext (hper t ht y) (hdper y)
    obtain ⟨y, hy, hxy⟩ := hjper.exists_mem_Ico₀ hL x
    exact ⟨(t, y), ⟨ht, hy.1, hy.2.le⟩, hxy.symm⟩
  have hDrcont : ContinuousOn (fderiv ℝ r) U :=
    (hr.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  have hPc : ContinuousOn P (U ×ˢ univ) :=
    (hr.continuousOn.comp continuous_fst.continuousOn (fun _ hz => hz.1)).prodMk
      ((hDrcont.comp continuous_fst.continuousOn (fun _ hz => hz.1)).clm_apply
        continuous_snd.continuousOn)
  have hK1 : IsCompact (P '' K0) :=
    hK0.image_of_continuousOn (hPc.mono (fun z hz => ⟨(hK0sub hz).1, mem_univ _⟩))
  have hK1sub : P '' K0 ⊆ Ω := by
    rintro z ⟨w, hw, rfl⟩
    have hwΩ := hK0sub hw
    refine ⟨heU (mem_range_self (ρ w.1)), ?_⟩
    change mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (ρ w.1))
      (fderiv ℝ (e ∘ ρ) w.1 w.2) ≠ 0
    rw [hDr w.1 hwΩ.1 w.2, hleft]
    exact hwΩ.2
  have hK : IsCompact K := hK0.union hK1
  have hKsub : K ⊆ Ω := union_subset hK0sub hK1sub
  obtain ⟨mu, Lambda, hmu, _hLambda, _LA, _LB, LD, hbounds, _hLA, _hLB, hLD⟩ :=
    ambientCurveCoefficients_uniform_bounds F he hU hρ hK hKsub
  have hphysical (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : a + t ∈ Icc a b :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hqswap : ContinuousOn (fun z : ℝ × ℝ => q z.2 z.1)
      (univ ×ˢ Icc (0 : ℝ) T) :=
    hqc.comp continuous_swap.continuousOn (fun _ hz => ⟨hz.2, hz.1⟩)
  have hpres : ∀ x t, t ∈ Icc (0 : ℝ) T → q t x = r (q t x) := by
    apply periodic_retraction_preservation
      (S := K) (p := L) (alpha := mu) (K := LD)
      (A := fun t => ambientCurvePrincipal F ρ (a + t))
      (B := fun t => ambientCurveLower F e ρ (a + t))
      (q := fun x t => q t x) (qx := fun x t => deriv (q t) x)
      (qxx := fun x t => iteratedDeriv 2 (q t) x)
      (qt := fun x t => ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
        iteratedDeriv 2 (q t) x +
          ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x))
      hL hT hmu hU (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (fun z _ => heU (mem_range_self (ρ z))) hqswap
      (fun x t ht => (hguard t ht x).1) hper
    · intro x t ht
      exact ((hspace t (Ioo_subset_Icc_self ht)).differentiable (by norm_num) x).hasDerivAt
    · intro x t ht
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      simpa only [iteratedDeriv_one] using
        ((hspace t (Ioo_subset_Icc_self ht)).differentiable_iteratedDeriv
          1 (by norm_num) x).hasDerivAt
    · intro x t ht
      exact htime t ht x
    · intro x t ht
      exact (hbounds (a + t) (hphysical t (Ioo_subset_Icc_self ht)) (j (t, x))
        (Or.inl (hjmem t (Ioo_subset_Icc_self ht) x))).1
    · intro x t ht
      rfl
    · intro x t ht
      exact Or.inl (hjmem t (Ioo_subset_Icc_self ht) x)
    · intro x t ht
      exact Or.inr (mem_image_of_mem P (hjmem t (Ioo_subset_Icc_self ht) x))
    · intro t ht
      exact hLD (a + t) (hphysical t (Ioo_subset_Icc_self ht))
    · intro x t ht
      exact ambientCurveCoefficients_retraction_defect F he hU heU hρ hρe (a + t)
        (hguard t (Ioo_subset_Icc_self ht) x).1 (deriv (q t) x)
    · exact hinit
  exact fun t ht x => hpres x t ht

end PoincareConjecture.M63
