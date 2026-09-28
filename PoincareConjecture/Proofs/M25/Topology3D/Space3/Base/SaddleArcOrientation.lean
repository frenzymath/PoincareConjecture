import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleOrientationPrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelField










set_option autoImplicit false

open Set Filter Function
open scoped ContDiff Manifold InnerProductSpace Matrix Topology

namespace PoincareConjecture.M25.Topology3D.SaddleOrientation

private theorem collar_arc_velocity
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (alpha : ℝ → UnitTwoSphere)
    (ha : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ alpha)
    (hai : ∀ t, Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) alpha t)) :
    let Gamma : ℝ → E3 := fun t => psi (alpha t, 0)
    ContDiff ℝ ∞ Gamma ∧ ∀ t, deriv Gamma t ≠ 0 := by
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let Gamma : ℝ → E3 := j ∘ alpha
  change ContDiff ℝ ∞ Gamma ∧ ∀ t, deriv Gamma t ≠ 0
  have hj := collar_central_contMDiff psi hpsi
  have hGamma : ContDiff ℝ ∞ Gamma := (hj.comp ha).contDiff
  refine ⟨hGamma, ?_⟩
  intro t
  have hd := (hj.mdifferentiable (by simp) (alpha t)).hasMFDerivAt.comp t
    (ha.mdifferentiable (by simp) t).hasMFDerivAt
  have hfd : fderiv ℝ Gamma t =
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) j (alpha t)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) alpha t) := by
    have hh := hd.mfderiv
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hi : Function.Injective (fderiv ℝ Gamma t) := by
    rw [hfd]
    exact (collar_central_mfderiv_injective psi hpsi (alpha t)).comp (hai t)
  intro hz
  have h10 : (1 : ℝ) = 0 := hi (by
    simpa only [fderiv_apply_one_eq_deriv, map_zero] using hz)
  exact one_ne_zero h10

private theorem collar_arc_orthogonality
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (rho : E3 → ℝ)
    (hrho : ContDiffOn ℝ ∞ rho (psi '' (univ ×ˢ Ioo (-1) 1)))
    (hrhopsi : ∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
      rho (psi p) = p.2)
    (u : E3) (z : ℝ) (alpha : ℝ → UnitTwoSphere)
    (ha : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ alpha)
    (hlevel : ∀ t, ⟪u, psi (alpha t, 0)⟫_ℝ = z) :
    let Gamma : ℝ → E3 := fun t => psi (alpha t, 0)
    ∀ t, ⟪gradient rho (Gamma t), deriv Gamma t⟫_ℝ = 0 ∧
      ⟪u, deriv Gamma t⟫_ℝ = 0 := by
  let Gamma : ℝ → E3 := fun t => psi (alpha t, 0)
  let U := psi '' (univ ×ˢ Ioo (-1) 1)
  change ∀ t, ⟪gradient rho (Gamma t), deriv Gamma t⟫_ℝ = 0 ∧
    ⟪u, deriv Gamma t⟫_ℝ = 0
  have hGamma : ContDiff ℝ ∞ Gamma :=
    ((collar_central_contMDiff psi hpsi).comp ha).contDiff
  have hGU (t : ℝ) : Gamma t ∈ U :=
    ⟨(alpha t, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hrG : rho ∘ Gamma = fun _ => (0 : ℝ) := by
    funext t
    exact hrhopsi (alpha t, 0) ⟨mem_univ _, by norm_num⟩
  have hHG : (InnerProductSpace.toDual ℝ E3 u) ∘ Gamma = fun _ => z :=
    funext hlevel
  intro t
  have hGt := (hGamma.differentiable (by simp) t).hasDerivAt
  have hrAt := (hrho.contDiffAt
    ((collar_image_open psi hpsi).mem_nhds (hGU t))).differentiableAt (by simp)
  constructor
  · have hd := hrAt.hasFDerivAt.comp_hasDerivAt t hGt
    have heq := hd.deriv
    rw [hrG, deriv_const] at heq
    rw [inner_gradient_left]
    exact heq.symm
  · have hd := (InnerProductSpace.toDual ℝ E3 u).hasFDerivAt.comp_hasDerivAt t hGt
    have heq := hd.deriv
    rw [hHG, deriv_const] at heq
    exact heq.symm




theorem collar_arc_orientation
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (rho : E3 → ℝ)
    (hrho : ContDiffOn ℝ ∞ rho (psi '' (univ ×ˢ Ioo (-1) 1)))
    (hrhopsi : ∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
      rho (psi p) = p.2)
    (hrhonz : ∀ y ∈ psi '' (univ ×ˢ Ioo (-1) 1), fderiv ℝ rho y ≠ 0)
    (u : E3) (z : ℝ) (alpha : ℝ → UnitTwoSphere)
    (ha : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ alpha)
    (hai : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) alpha t))
    (hlevel : ∀ t, ⟪u, psi (alpha t, 0)⟫_ℝ = z)
    (hreg : ∀ t, mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪u, psi (p, 0)⟫_ℝ) (alpha t) ≠ 0) :
    let Gamma : ℝ → E3 := fun t => psi (alpha t, 0)
    let J : ℝ → ℝ := fun t =>
      ⟪heightCrossMap u (gradient rho (Gamma t)), deriv Gamma t⟫_ℝ
    Continuous J ∧ (∀ t, J t ≠ 0) ∧ 0 < J 0 * J 1 := by
  obtain ⟨hGamma, hvelocity⟩ := collar_arc_velocity psi hpsi alpha ha hai
  have hperp := collar_arc_orthogonality psi hpsi rho hrho hrhopsi u z alpha ha hlevel
  let U := psi '' (univ ×ˢ Ioo (-1) 1)
  let Gamma : ℝ → E3 := fun t => psi (alpha t, 0)
  let J : ℝ → ℝ := fun t =>
    ⟪heightCrossMap u (gradient rho (Gamma t)), deriv Gamma t⟫_ℝ
  have hGU (t : ℝ) : Gamma t ∈ U :=
    ⟨(alpha t, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hn : Continuous (fun t => gradient rho (Gamma t)) := by
    have hh : ContinuousOn (gradient rho) U :=
      (contDiffOn_gradient_of_isOpen (collar_image_open psi hpsi) rho hrho).continuousOn
    exact hh.comp_continuous hGamma.continuous hGU
  have hJcont : Continuous J :=
    ((heightCrossMap u).continuous.comp hn).inner
      (hGamma.continuous_deriv (by simp))
  have hJnz (t : ℝ) : J t ≠ 0 := by
    let n := WithLp.ofLp (gradient rho (Gamma t))
    let v := WithLp.ofLp (deriv Gamma t)
    let w := WithLp.ofLp u
    have hcross : n ⨯₃ w ≠ 0 := by
      intro hz
      apply collar_regular_height_cross_ne_zero psi hpsi rho hrho hrhopsi
        hrhonz u (alpha t) (hreg t)
      rw [heightCrossMap_apply]
      change WithLp.toLp 2 (n ⨯₃ w) = 0
      rw [hz]
      rfl
    have hv : v ≠ 0 := by
      intro hz
      apply hvelocity t
      exact (EuclideanSpace.equiv (Fin 3) ℝ).injective
        (hz.trans (map_zero (EuclideanSpace.equiv (Fin 3) ℝ)).symm)
    have hnv : n ⬝ᵥ v = 0 := by
      have h := (hperp t).1
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
      exact (dotProduct_comm n v).trans h
    have hwv : w ⬝ᵥ v = 0 := by
      have h := (hperp t).2
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
      exact (dotProduct_comm w v).trans h
    have hJform : J t = v ⬝ᵥ (n ⨯₃ w) := by
      dsimp only [J, v, n, w]
      rw [heightCrossMap_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [hJform, triple_product_permutation v n w]
    exact triple_ne_zero_of_transverse n w v hcross hv hnv hwv
  exact ⟨hJcont, hJnz, mul_pos_of_connected_nonzero
    (isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) 1))
    hJcont.continuousOn (fun t _ => hJnz t)
    (by constructor <;> norm_num) (by constructor <;> norm_num)⟩

end PoincareConjecture.M25.Topology3D.SaddleOrientation
