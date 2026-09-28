import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightHessian

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem collar_height_hessian_injective (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (N : UnitTwoSphere → UnitTwoSphere)
    (hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N)
    (hnormal : ∀ (p : UnitTwoSphere) (a : TangentSpace (𝓡 2) p),
      ⟪(N p : E3), mfderiv (𝓡 2) 𝓘(ℝ, E3)
        (fun z : UnitTwoSphere => ψ (z, 0)) p a⟫_ℝ = 0)
    (u q : UnitTwoSphere)
    (hcritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0)
    (hregular : Function.Injective (mfderiv (𝓡 2) (𝓡 2) N q)) :
    Function.Injective (fderiv ℝ (fderiv ℝ (fun y : E2 =>
      ⟪(u : E3), ψ ((chartAt E2 q).symm y, 0)⟫_ℝ)) (chartAt E2 q q)) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let c := chartAt E2 q
  let e : UnitTwoSphere → E3 := fun p => ψ (p, 0)
  let ec : E2 → E3 := e ∘ c.symm
  let nc : E2 → E3 := fun y => (N (c.symm y) : E3)
  let i : UnitTwoSphere → E3 := fun p => (p : E3)
  have hqc : q ∈ c.source := mem_chart_source E2 q
  have hx : c q ∈ c.target := c.map_source hqc
  have hcs : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ c.symm c.target := contMDiffOn_chart_symm
  have he : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ e := collar_central_contMDiff ψ hψ
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ i := contMDiff_coe_sphere
  have hec : ContDiffOn ℝ ∞ ec c.target := (he.comp_contMDiffOn hcs).contDiffOn
  have hnc : ContDiffOn ℝ ∞ nc c.target := ((hi.comp hN).comp_contMDiffOn hcs).contDiffOn
  have hc := (mdifferentiable_chart (I := 𝓡 2) q).symm
  have hde (y : E2) (hy : y ∈ c.target) : fderiv ℝ ec y =
      (mvfderiv (𝓡 2) e (c.symm y)).comp (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm y) := by
    have hd : HasMFDerivAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) ec y
        ((mfderiv (𝓡 2) 𝓘(ℝ, E3) e (c.symm y)).comp
          (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm y)) :=
      (he.mdifferentiable (by simp) (c.symm y)).hasMFDerivAt.comp y
        (hc.mdifferentiableAt hy).hasMFDerivAt
    rw [← mfderiv_eq_fderiv]
    exact hd.mfderiv
  have hdn (y : E2) (hy : y ∈ c.target) : fderiv ℝ nc y =
      (mvfderiv (𝓡 2) i (N (c.symm y))).comp
        ((mfderiv (𝓡 2) (𝓡 2) N (c.symm y)).comp
          (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm y)) := by
    have hd : HasMFDerivAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) nc y
        (((mfderiv (𝓡 2) 𝓘(ℝ, E3) i (N (c.symm y))).comp
          (mfderiv (𝓡 2) (𝓡 2) N (c.symm y))).comp
            (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm y)) :=
      ((hi.mdifferentiable (by simp) (N (c.symm y))).hasMFDerivAt.comp (c.symm y)
        (hN.mdifferentiable (by simp) (c.symm y)).hasMFDerivAt).comp y
          (hc.mdifferentiableAt hy).hasMFDerivAt
    rw [← mfderiv_eq_fderiv]
    exact hd.mfderiv
  have hecinj : Function.Injective (fderiv ℝ ec (c q)) := by
    rw [hde (c q) hx]
    apply Function.Injective.comp _ (hc.mfderiv_bijective hx).injective
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (e (c.symm (c q)))).injective.comp
      (collar_central_mfderiv_injective ψ hψ (c.symm (c q)))
  have hncinj : Function.Injective (fderiv ℝ nc (c q)) := by
    rw [hdn (c q) hx]
    apply (injective_mvfderiv_subtypeVal_sphere (N (c.symm (c q)))).comp
    apply Function.Injective.comp _ (hc.mfderiv_bijective hx).injective
    change Function.Injective (mfderiv (𝓡 2) (𝓡 2) N (c.symm (c q)))
    rw [c.left_inv hqc]
    exact hregular
  have horth (y : E2) (hy : y ∈ c.target) (b : E2) :
      ⟪nc y, fderiv ℝ ec y b⟫_ℝ = 0 := by
    rw [hde y hy]
    exact hnormal (c.symm y) (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm y b)
  obtain ⟨σ, hσ, hu⟩ : ∃ σ : ℝ, σ ≠ 0 ∧ (u : E3) = σ • nc (c q) := by
    rcases (collar_height_critical_iff ψ hψ q (N q) u (hnormal q)).mp hcritical with hp | hm
    · refine ⟨1, one_ne_zero, ?_⟩
      simpa only [nc, c.left_inv hqc, one_smul] using hp
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
      simpa only [nc, c.left_inv hqc, neg_one_smul] using hm
  have hess := height_hessian_injective ec nc c.open_target hec hnc
    (fun y _ => norm_eq_of_mem_sphere (N (c.symm y))) horth hx hecinj
    (by simp [E2, E3]) hncinj σ hσ
  have hfunc : (fun y : E2 => ⟪(u : E3), ψ (c.symm y, 0)⟫_ℝ) =
      fun y => ⟪σ • nc (c q), ec y⟫_ℝ := by
    funext y
    exact congrArg (fun w : E3 => ⟪w, ec y⟫_ℝ) hu
  change Function.Injective (fderiv ℝ (fderiv ℝ
    (fun y : E2 => ⟪(u : E3), ψ (c.symm y, 0)⟫_ℝ)) (c q))
  rw [hfunc]
  exact hess

end PoincareConjecture.M25.Topology3D
