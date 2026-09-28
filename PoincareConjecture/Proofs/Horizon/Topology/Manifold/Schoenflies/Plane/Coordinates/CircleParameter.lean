import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Tube.SphereTangent
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv











set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def sphereCircleParameter (e : ℂ ≃ₗᵢ[ℝ] E) (s : ℝ) : sphere (0 : E) 1 :=
  ⟨e (Circle.exp s : ℂ), by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    exact Circle.norm_coe _⟩


theorem periodic_sphereCircleParameter (e : ℂ ≃ₗᵢ[ℝ] E) :
    Periodic (sphereCircleParameter e) (2 * Real.pi) := by
  intro s
  apply Subtype.ext
  exact congrArg (fun q : Circle => e (q : ℂ)) (Circle.periodic_exp s)



theorem surjective_sphereCircleParameter (e : ℂ ≃ₗᵢ[ℝ] E) :
    Surjective (sphereCircleParameter e) := by
  intro q
  let p : Circle := ⟨e.symm (q : E), by
    exact mem_sphere_zero_iff_norm.mpr
      ((e.symm.norm_map (q : E)).trans (norm_eq_of_mem_sphere q))⟩
  obtain ⟨s, hs⟩ := Circle.exp_surjective p
  refine ⟨s, Subtype.ext ?_⟩
  change e (Circle.exp s : ℂ) = (q : E)
  rw [hs]
  exact e.apply_symm_apply _



theorem injOn_sphereCircleParameter_Ico (e : ℂ ≃ₗᵢ[ℝ] E) {a b : ℝ}
    (hab : b - a ≤ 2 * Real.pi) : InjOn (sphereCircleParameter e) (Ico a b) := by
  intro s hs t ht h
  apply Circle.exp_injOn_Ico hab hs ht
  apply Subtype.ext
  apply e.injective
  exact congrArg Subtype.val h



theorem hasDerivAt_sphereCircleParameter_coe (e : ℂ ≃ₗᵢ[ℝ] E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (sphereCircleParameter e t : E))
      (e (Complex.I * (Circle.exp s : ℂ))) s := by
  have h : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.I * (Circle.exp s : ℂ)) s := by
    simpa only [id_eq, Complex.ofReal_one, one_mul, mul_one, Circle.coe_exp, mul_comm] using
      (((hasDerivAt_id s).ofReal_comp).mul_const Complex.I).cexp
  exact e.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt s h

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]



theorem contMDiff_sphereCircleParameter (e : ℂ ≃ₗᵢ[ℝ] E) {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) k (sphereCircleParameter e) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) k (fun s : ℝ => e (Circle.exp s : ℂ)) :=
    e.contDiff.contMDiff.comp
      ((contMDiff_coe_sphere (E := ℂ) (n := 1) (m := k)).comp contMDiff_circleExp)
  exact h.codRestrict_sphere (n := 1) (fun s => (sphereCircleParameter e s).property)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem contDiff_curveFamily_circleParameter (e : ℂ ≃ₗᵢ[ℝ] E)
    (c : ℝ → sphere (0 : E) 1 → F) {k : ℕ∞ω}
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, F) k
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2)) :
    ContDiff ℝ k (fun p : ℝ × ℝ => c p.1 (sphereCircleParameter e p.2)) := by
  exact (hc.comp (contDiff_fst.contMDiff.prodMk
    ((contMDiff_sphereCircleParameter e).comp contDiff_snd.contMDiff))).contDiff




theorem deriv_curveFamily_circleParameter_ne_zero (e : ℂ ≃ₗᵢ[ℝ] E)
    (c : ℝ → sphere (0 : E) 1 → F)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    (z s : ℝ) (hi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, F) (c z) (sphereCircleParameter e s))) :
    deriv (fun t : ℝ => c z (sphereCircleParameter e t)) s ≠ 0 := by
  let : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  let q := sphereCircleParameter e s
  let q0 := sphereCircleParameter e 0
  let v := e (Complex.I * (Circle.exp s : ℂ))
  let G : E → F := fun x => radialFamilyExtension q0 c (z, x)
  have hvnorm : ‖v‖ = 1 := by
    simp only [v, e.norm_map, norm_mul, Complex.norm_I, Circle.norm_coe, one_mul]
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; norm_num)
  have hv : v ∈ (ℝ ∙ (q : E))ᗮ := by
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left).mpr
    change inner ℝ (e (Complex.I * (Circle.exp s : ℂ))) (e (Circle.exp s : ℂ)) = 0
    rw [e.inner_map_map, ← Complex.rightAngleRotation]
    exact Complex.orientation.inner_rightAngleRotation_self _
  have hC := contDiffOn_radialFamilyExtension (n := 1) (m := ∞) q0 c hc
  have hp : (z, (q : E)) ∈ (univ : Set ℝ) ×ˢ ({0} : Set E)ᶜ :=
    ⟨mem_univ z, ne_zero_of_mem_unit_sphere q⟩
  have ho : IsOpen ((univ : Set ℝ) ×ˢ ({0} : Set E)ᶜ) :=
    isOpen_univ.prod isClosed_singleton.isOpen_compl
  have hG : DifferentiableAt ℝ G (q : E) :=
    ((hC.contDiffAt (ho.mem_nhds hp)).comp (q : E)
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hGc : ∀ p : sphere (0 : E) 1, G (p : E) = c z p :=
    fun p => radialFamilyExtension_apply_sphere q0 c z p
  have hnonzero := fderiv_ne_zero_of_sphere_immersion q hG hGc hi hv hv0
  have hder := hG.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_sphereCircleParameter_coe e s)
  have hfun : (G ∘ fun t : ℝ => (sphereCircleParameter e t : E)) =
      (fun t : ℝ => c z (sphereCircleParameter e t)) := funext (fun t => hGc _)
  rw [hfun] at hder
  rw [hder.deriv]
  exact hnonzero

end InnerProduct

end Poincare.Manifold.Schoenflies.Plane
