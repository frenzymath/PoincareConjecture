import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeightHessian
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalBranches
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CriticalBranchHeight
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FiniteValueSeparation

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_generic_collar_height (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) :
    ∃ u : UnitTwoSphere,
      {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0}.Finite ∧
      InjOn (fun q : UnitTwoSphere => ⟪(u : E3), ψ (q, 0)⟫_ℝ)
        {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0} ∧
      ∀ q : UnitTwoSphere,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0 →
          Function.Injective (fderiv ℝ (fderiv ℝ (fun y : E2 =>
            ⟪(u : E3), ψ ((chartAt E2 q).symm y, 0)⟫_ℝ)) (chartAt E2 q q)) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  obtain ⟨N, u, hN, hnormal, hregular⟩ := exists_sphere_collar_regular_normal ψ hψ
  obtain ⟨hfp, hfm, W, g, hW, huW, hg, hNg, hall, hginj, hgreg⟩ :=
    exists_opposite_normal_branches N hN u (fun q hq => by
      apply hregular q
      rcases hq with hp | hm
      · exact Or.inl (congrArg Subtype.val hp)
      · exact Or.inr (congrArg Subtype.val hm))
  let : Finite (N ⁻¹' {u}) := hfp
  let : Finite (N ⁻¹' {-u}) := hfm
  let ι := (N ⁻¹' {u}) ⊕ (N ⁻¹' {-u})
  let e : UnitTwoSphere → E3 := fun p => ψ (p, 0)
  have he : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ e := collar_central_contMDiff ψ hψ
  have heinj : Function.Injective e := by
    intro a b hab
    exact congrArg Prod.fst (hψ.2.1 ⟨mem_univ _, by norm_num⟩
      ⟨mem_univ _, by norm_num⟩ hab)
  have hcritical (i : ι) (v : UnitTwoSphere) (hv : v ∈ W) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p => ⟪(v : E3), e p⟫_ℝ) (g i v) = 0 := by
    apply (collar_height_critical_iff ψ hψ (g i v) (N (g i v)) v (hnormal (g i v))).mpr
    rcases hNg i v hv with hp | hm
    · exact Or.inl (congrArg Subtype.val hp).symm
    · right
      simpa only [coe_neg_sphere, neg_neg] using
        (congrArg Neg.neg (congrArg Subtype.val hm)).symm
  have hcomplete (v : UnitTwoSphere) (hv : v ∈ W) (q : UnitTwoSphere)
      (hq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p => ⟪(v : E3), e p⟫_ℝ) q = 0) :
      ∃ i : ι, g i v = q := by
    apply hall v hv q
    rcases (collar_height_critical_iff ψ hψ q (N q) v (hnormal q)).mp hq with hp | hm
    · exact Or.inl (Subtype.ext hp.symm)
    · right
      apply Subtype.ext
      simpa only [coe_neg_sphere, neg_neg] using (congrArg Neg.neg hm).symm
  let H : ι → UnitTwoSphere → ℝ := fun i v => ⟪(v : E3), e (g i v)⟫_ℝ
  have hH (i : ι) : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (H i) W :=
    (contDiff_inner : ContDiff ℝ ∞ (fun p : E3 × E3 => ⟪p.1, p.2⟫_ℝ)).contMDiff.comp_contMDiffOn
      ((contMDiff_coe_sphere : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ _).contMDiffOn.prodMk_space
        (he.comp_contMDiffOn (hg i)))
  obtain ⟨v, hv, hsep⟩ := exists_injective_values_of_regular_differences (𝓡 2) H hW
    ⟨u, huW⟩ (fun i => (hH i).continuousOn) (by
      intro i j hij v hv heq
      exact criticalBranch_height_difference_nonzero e he heinj (g i) (g j) v
        (((hg i).contMDiffAt (hW.mem_nhds hv)).mdifferentiableAt (by simp))
        (((hg j).contMDiffAt (hW.mem_nhds hv)).mdifferentiableAt (by simp))
        (hcritical i v hv) (hcritical j v hv) (fun h => hij (hginj v hv h)) heq)
  refine ⟨v, (finite_range (fun i : ι => g i v)).subset ?_, ?_, ?_⟩
  · intro q hq
    exact hcomplete v hv q hq
  · intro q hq r hr hqr
    obtain ⟨i, hi⟩ := hcomplete v hv q hq
    obtain ⟨j, hj⟩ := hcomplete v hv r hr
    have hij : i = j := hsep (by
      change ⟪(v : E3), e (g i v)⟫_ℝ = ⟪(v : E3), e (g j v)⟫_ℝ
      rw [hi, hj]
      exact hqr)
    exact hi.symm.trans ((congrArg (fun k : ι => g k v) hij).trans hj)
  · intro q hq
    obtain ⟨i, rfl⟩ := hcomplete v hv q hq
    exact collar_height_hessian_injective ψ hψ N hN hnormal v (g i v) hq
      (hgreg i v hv)

end PoincareConjecture.M25.Topology3D
