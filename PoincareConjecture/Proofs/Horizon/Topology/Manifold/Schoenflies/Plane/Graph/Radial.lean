import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Periodic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

theorem exists_ambient_diffeomorph_of_positive_radial_graph
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    (R : sphere (0 : E) 1 → ℝ) (hR : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ R)
    (hpos : ∀ q, 0 < R q) :
    ∃ F : E ≃ₘ[ℝ] E,
      (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      F '' sphere (0 : E) 1 = range (fun q => R q • (q : E)) := by
  let r : ℝ → ℝ → ℝ := fun t s => 1 - t + t * R (sphereCircleParameter e s)
  let γ : ℝ → ℝ → E := fun t s => r t s • (sphereCircleParameter e s : E)
  have hr : ContDiff ℝ ∞ (fun x : ℝ × ℝ => r x.1 x.2) :=
    (contDiff_const.sub contDiff_fst).add
      (contDiff_fst.mul ((hR.comp (contMDiff_sphereCircleParameter e)).contDiff.comp contDiff_snd))
  have hq : ContDiff ℝ ∞ (fun s : ℝ => (sphereCircleParameter e s : E)) :=
    ((contMDiff_coe_sphere (E := E) (n := 1) (m := ∞)).comp
      (contMDiff_sphereCircleParameter e)).contDiff
  have hγ : ContDiff ℝ ∞ (fun x : ℝ × ℝ => γ x.1 x.2) :=
    hr.smul (hq.comp contDiff_snd)
  have hrpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ) : 0 < r t s := by
    dsimp [r]
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have := mul_pos htpos (hpos (sphereCircleParameter e s))
      linarith [ht.2]
  have hper (t : ℝ) : Periodic (γ t) (2 * Real.pi) := by
    intro s
    simp only [γ, r, periodic_sphereCircleParameter e s]
  have hinj (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      InjOn (γ t) (Ico 0 (2 * Real.pi)) := by
    intro s hs u hu heq
    have hnorm (v : ℝ) : ‖γ t v‖ = r t v := by
      simp only [γ, norm_smul, Real.norm_eq_abs, abs_of_pos (hrpos t ht v),
        norm_eq_of_mem_sphere, mul_one]
    have hradius : r t s = r t u := by
      simpa only [hnorm] using congrArg norm heq
    have hpoints : sphereCircleParameter e s = sphereCircleParameter e u := by
      apply Subtype.ext
      change r t s • (sphereCircleParameter e s : E) =
        r t u • (sphereCircleParameter e u : E) at heq
      rw [← hradius] at heq
      exact (smul_right_injective _ (hrpos t ht s).ne') heq
    exact injOn_sphereCircleParameter_Ico e (by simp) hs hu hpoints
  have hregular (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ) : deriv (γ t) s ≠ 0 := by
    have hrs : ContDiff ℝ ∞ (r t) :=
      hr.comp (f := fun v : ℝ => (t, v)) (contDiff_const.prodMk contDiff_id)
    have hd := (hrs.differentiable (by simp) s).hasDerivAt.smul
      (hasDerivAt_sphereCircleParameter_coe e s)
    have hder : deriv (γ t) s = deriv (r t) s • (sphereCircleParameter e s : E) +
        r t s • e (Complex.I * (Circle.exp s : ℂ)) := by
      simpa only [γ, Pi.smul_def', add_comm] using hd.deriv
    intro hz
    rw [hder] at hz
    have hcomplex := congrArg e.symm hz
    change e.symm (deriv (r t) s • e (Circle.exp s : ℂ) +
      r t s • e (Complex.I * (Circle.exp s : ℂ))) = e.symm 0 at hcomplex
    simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply, map_zero,
      Complex.real_smul] at hcomplex
    have hfactor : (((deriv (r t) s : ℝ) : ℂ) + (r t s : ℂ) * Complex.I) *
        (Circle.exp s : ℂ) = 0 := by
      rw [add_mul, mul_assoc]
      exact hcomplex
    have hnonzero : (Circle.exp s : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hzero := (mul_eq_zero.mp hfactor).resolve_right hnonzero
    have him := congrArg Complex.im hzero
    have : r t s = 0 := by simpa using him
    exact (hrpos t ht s).ne' this
  obtain ⟨Phi, _, _, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_periodic_family e o (by positivity) zero_le_one γ
      hγ hper hinj hregular
  have hzero : range (γ 0) = sphere (0 : E) 1 := by
    have hval : range (fun q : sphere (0 : E) 1 => (q : E)) = sphere (0 : E) 1 :=
      Subtype.range_coe_subtype
    rw [← hval, ← (surjective_sphereCircleParameter e).range_comp]
    congr 1
    funext s
    simp [γ, r]
  have hone : range (γ 1) = range (fun q => R q • (q : E)) := by
    rw [← (surjective_sphereCircleParameter e).range_comp (fun q => R q • (q : E))]
    congr 1
    funext s
    simp [γ, r]
  refine ⟨Phi 1, ⟨K, hK, hfix 1⟩, ?_⟩
  simpa only [hzero, hone] using hmotion 1 (by simp)

end Poincare.Manifold.Schoenflies.Plane
