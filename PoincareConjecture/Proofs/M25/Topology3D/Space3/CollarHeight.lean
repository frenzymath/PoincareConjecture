import PoincareConjecture.Proofs.M25.Topology3D.Space3.GaussNormal
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NormalPlane
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularFibers

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem collar_central_contMDiff (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (fun q : UnitTwoSphere => ψ (q, 0)) := by
  apply contMDiffOn_univ.mp
  exact hψ.1.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
    (fun _ _ => ⟨mem_univ _, by norm_num⟩)

theorem collar_central_mfderiv_injective (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (q : UnitTwoSphere) :
    Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun p : UnitTwoSphere => ψ (p, 0)) q) := by
  obtain ⟨e, he, hes, _, hei⟩ := exists_collar_chart ψ hψ
  let f : UnitTwoSphere → E3 := fun p => ψ (p, 0)
  let k : E3 → UnitTwoSphere := fun y => (e.symm y).1
  have hs (p : UnitTwoSphere) : (p, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, by norm_num⟩
  have ht (p : UnitTwoSphere) : f p ∈ e.target := by
    change ψ (p, 0) ∈ e.target
    rw [← he]
    exact e.map_source (hs p)
  have hleft : k ∘ f = id := by
    funext p
    change (e.symm (ψ (p, 0))).1 = p
    rw [← he, e.left_inv (hs p)]
  have hk : ContMDiffAt 𝓘(ℝ, E3) (𝓡 2) ∞ k (f q) :=
    contMDiff_fst.contMDiffAt.comp _ (hei.contMDiffAt (e.open_target.mem_nhds (ht q)))
  have hd := (hk.mdifferentiableAt (by simp)).hasMFDerivAt.comp q
    ((collar_central_contMDiff ψ hψ).mdifferentiable (by simp) q).hasMFDerivAt
  have hmap := hd.mfderiv
  rw [hleft, mfderiv_id] at hmap
  intro a b hab
  have ha := congrArg (fun A => A a) hmap
  have hb := congrArg (fun A => A b) hmap
  exact ha.trans ((congrArg (mfderiv 𝓘(ℝ, E3) (𝓡 2) k (f q)) hab).trans hb.symm)

theorem collar_height_critical_iff (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (q : UnitTwoSphere) (n u : UnitTwoSphere)
    (hnormal : ∀ v : TangentSpace (𝓡 2) q,
      ⟪(n : E3), mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun p : UnitTwoSphere => ψ (p, 0)) q v⟫_ℝ = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0 ↔
      (u : E3) = (n : E3) ∨ (u : E3) = -(n : E3) := by
  let A : E2 →L[ℝ] E3 :=
    mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun p : UnitTwoSphere => ψ (p, 0)) q
  have hd := (InnerProductSpace.toDual ℝ E3 (u : E3)).hasFDerivAt.hasMFDerivAt.comp q
    ((collar_central_contMDiff ψ hψ).mdifferentiable (by simp) q).hasMFDerivAt
  have hcriterion := height_annihilates_iff_normal_sign (V := E2) A
    (collar_central_mfderiv_injective ψ hψ q) (by simp [E2, E3])
    (n : E3) (u : E3) (norm_eq_of_mem_sphere n) (norm_eq_of_mem_sphere u) hnormal
  constructor
  · intro hzero
    apply hcriterion.mp
    intro v
    have h := congrArg (fun L => L v) (hd.mfderiv.symm.trans hzero)
    exact h
  · intro hsign
    refine hd.mfderiv.trans ?_
    apply ContinuousLinearMap.ext
    intro v
    exact hcriterion.mpr hsign v

theorem exists_finite_collar_height_critical_points (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) :
    ∃ u : UnitTwoSphere,
      {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0}.Finite := by
  obtain ⟨N, u, hN, hnormal, hregular⟩ := exists_sphere_collar_regular_normal ψ hψ
  have hpos := finite_regular_fiber N hN u (fun q hq =>
    hregular q (Or.inl (congrArg Subtype.val hq)))
  have hneg := finite_regular_fiber N hN (-u) (fun q hq =>
    hregular q (Or.inr (congrArg Subtype.val hq)))
  refine ⟨u, (hpos.union hneg).subset ?_⟩
  intro q hq
  rcases (collar_height_critical_iff ψ hψ q (N q) u (hnormal q)).mp hq with hp | hn
  · left
    exact Subtype.ext hp.symm
  · right
    apply Subtype.ext
    simpa only [coe_neg_sphere, neg_neg] using (congrArg Neg.neg hn).symm

end PoincareConjecture.M25.Topology3D
