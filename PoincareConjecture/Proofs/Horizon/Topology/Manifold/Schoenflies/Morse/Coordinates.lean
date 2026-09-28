import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Height
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Hessian
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.NormalForm
import Mathlib.Analysis.InnerProductSpace.Dual



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private theorem fderiv_sphere_parametrization_apply
    {f : S2 -> E3} (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    {c : E2 -> S2} (hc : ContMDiff (𝓡 2) (𝓡 2) ∞ c) (x u : E2) :
    fderiv Real (f ∘ c) x u =
      mfderiv (𝓡 2) (𝓡 3) f (c x) (mfderiv (𝓡 2) (𝓡 2) c x u) := by
  have h := mfderiv_comp x ((hf (c x)).mdifferentiableAt (by simp))
    ((hc x).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at h
  exact congrArg (fun A : E2 →L[Real] E3 => A u) h



theorem exists_height_coordinates_of_regular_normal
    {f : S2 -> E3} (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    (N : S2 -> S2) (hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N)
    (hspan : ∀ (p : S2) (w : E3),
      (∀ u, inner Real w (mfderiv (𝓡 2) (𝓡 3) f p u) = 0) ↔
        ∃ c : Real, w = c • (N p : E3))
    (p : S2) (hreg : Function.Bijective (mfderiv (𝓡 2) (𝓡 2) N p)) :
    ∃ (e : OpenPartialHomeomorph E2 S2) (σ : Fin 2 -> Real),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, inner Real (N p : E3) (f (e x)) =
        inner Real (N p : E3) (f p) + ∑ i : Fin 2, σ i * x i ^ 2 := by
  let b := stereographic' 2 (-p)
  have hb : b ∈ maximalAtlas (𝓡 2) ∞ S2 := by
    apply IsManifold.subset_maximalAtlas
    exact ⟨-p, rfl⟩
  have hb0 : b p = 0 := by
    have h (q : S2) : stereographic' 2 q (-q) = 0 := by
      simp [stereographic', stereographic_apply_neg]
    simpa only [b, neg_neg] using h (-p)
  have hp : p ∈ b.source := by simp [b, ne_neg_of_mem_unit_sphere Real p]
  have hc0 : b.symm 0 = p := by simpa only [hb0] using b.left_inv hp
  have hc : ContMDiff (𝓡 2) (𝓡 2) ∞ b.symm := by
    rw [← contMDiffOn_univ]
    simpa only [b, stereographic'_target] using contMDiffOn_symm_of_mem_maximalAtlas hb
  let d : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := b.symm.toPartialEquiv
    open_source := b.open_target
    open_target := b.open_source
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hb
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hb }
  have hcloc (x : E2) : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ b.symm x :=
    ⟨d, by simp [d, b], fun _ _ => rfl⟩
  have hcbij (x : E2) : Function.Bijective (mfderiv (𝓡 2) (𝓡 2) b.symm x) :=
    ((hcloc x).mfderivToContinuousLinearEquiv (by simp)).bijective
  let g : E2 -> E3 := f ∘ b.symm
  let n : E2 -> E3 := fun x => (N (b.symm x) : E3)
  have hg : ContDiff Real ∞ g := (hf.comp hc).contDiff
  have hNa : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => (N q : E3)) :=
    contMDiff_coe_sphere.comp hN
  have hn : ContDiff Real ∞ n := (hNa.comp hc).contDiff
  have hn0 : n 0 = (N p : E3) := by simp only [n, hc0]
  have hunit (x : E2) : ‖n x‖ = 1 := norm_eq_of_mem_sphere (N (b.symm x))
  have horth (x u : E2) : inner Real (n x) (fderiv Real g x u) = 0 := by
    rw [fderiv_sphere_parametrization_apply hf hc]
    exact (hspan (b.symm x) (N (b.symm x))).mpr ⟨1, by simp⟩ _
  have hspan0 (w : E3) (hw : ∀ u, inner Real w (fderiv Real g 0 u) = 0) :
      ∃ c : Real, w = c • n 0 := by
    rw [hn0]
    apply (hspan p w).mp
    intro v
    obtain ⟨u, hu⟩ := (hcbij 0).surjective v
    have h := hw u
    rw [fderiv_sphere_parametrization_apply hf hc, hu, hc0] at h
    exact h
  have hNchain (u : TangentSpace (𝓡 2) p) :
      mfderiv (𝓡 2) (𝓡 3) (fun q => (N q : E3)) p u =
        mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 -> E3) (N p)
          (mfderiv (𝓡 2) (𝓡 2) N p u) := by
    have h := mfderiv_comp p ((contMDiff_coe_sphere (n := 2) (N p)).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp)) ((hN p).mdifferentiableAt (by simp))
    exact congrArg (fun A : TangentSpace (𝓡 2) p →L[Real] E3 => A u) h
  have hinj : Function.Injective (fderiv Real n 0) := by
    intro u v huv
    apply (hcbij 0).injective
    apply hreg.injective
    have hcoe : Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 -> E3) (N p)) := by
      convert! injective_mvfderiv_subtypeVal_sphere (N p)
    apply hcoe
    have hd (u : E2) : fderiv Real n 0 u =
        mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 -> E3) (N p)
          (mfderiv (𝓡 2) (𝓡 2) N p (mfderiv (𝓡 2) (𝓡 2) b.symm 0 u)) := by
      have h := fderiv_sphere_parametrization_apply hNa hc 0 u
      rw [hc0, hNchain] at h
      exact h
    simpa only [hd] using huv
  let h : E2 -> Real := fun x => inner Real (n 0) (g x)
  have hh : ContDiff Real ∞ h := contDiff_const.inner Real hg
  have hhcrit : fderiv Real h 0 = 0 := by
    ext u
    have he := ((innerSL Real (n 0)).hasFDerivAt.comp 0
      (hg.differentiable (by simp) 0).hasFDerivAt).fderiv
    exact (congrArg (fun A : E2 →L[Real] Real => A u) he).trans (horth 0 u)
  have hHinj := injective_height_hessian_of_regular_normal hg hn hunit horth 0 hspan0 hinj
  have hH : Function.Bijective (fderiv Real (fderiv Real h) 0) := by
    refine ⟨hHinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hHinj⟩
    exact (InnerProductSpace.toDual Real E2).toLinearEquiv.finrank_eq
  obtain ⟨a, σ, hσ, ha0, hazero, ha, hai, hform⟩ :=
    Poincare.Analysis.Calculus.Morse.exists_smooth_morse_coordinates_two hh hhcrit hH
  let e := a.trans b.symm
  refine ⟨e, σ, hσ, ⟨ha0, by simp [b]⟩, ?_, ?_, ?_, ?_⟩
  · change b.symm (a 0) = p
    rw [hazero, hc0]
  · exact hc.comp_contMDiffOn (ha.contMDiffOn.mono inter_subset_left)
  · exact hai.contMDiffOn.comp (contMDiffOn_of_mem_maximalAtlas hb |>.mono inter_subset_left)
      (fun _ hx => hx.2)
  · intro x hx
    change inner Real (N p : E3) (f (b.symm (a x))) = _
    simpa only [h, g, Function.comp_apply, hn0, hc0] using hform x hx.1



theorem exists_morse_height
    (f : sphere (0 : EuclideanSpace Real (Fin 3)) 1 ->
      EuclideanSpace Real (Fin 3))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ v : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      {p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 |
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0}.Finite ∧
      ∀ p : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0 ->
        ∃ (e : OpenPartialHomeomorph (EuclideanSpace Real (Fin 2))
            (sphere (0 : EuclideanSpace Real (Fin 3)) 1)) (σ : Fin 2 -> Real),
          (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          ∀ x ∈ e.source, inner Real (v : EuclideanSpace Real (Fin 3)) (f (e x)) =
            inner Real (v : EuclideanSpace Real (Fin 3)) (f p) +
              ∑ i : Fin 2, σ i * x i ^ 2 := by
  obtain ⟨N, hN, hnormal⟩ := exists_smooth_unit_normal f hf
  have hne : (univ : Set S2).Nonempty := by
    obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E3))).mpr
      (by norm_num : (0 : Real) ≤ 1)
    exact ⟨⟨v, hv⟩, mem_univ _⟩
  obtain ⟨v, _, hv, hnv⟩ := exists_antipodal_regular_values_sphere hN isOpen_univ hne
  refine ⟨v, ((finite_fiber_of_regular_value_sphere hN hv).union
    (finite_fiber_of_regular_value_sphere hN hnv)).subset ?_, ?_⟩
  · intro p hp
    exact (height_critical_iff_normal hf.contMDiff N hnormal v p).mp hp
  · intro p hp
    have hcases := (height_critical_iff_normal hf.contMDiff N hnormal v p).mp hp
    have hreg : Function.Bijective (mfderiv (𝓡 2) (𝓡 2) N p) :=
      hcases.elim (hv p) (hnv p)
    obtain ⟨e, σ, hσ, he0, hezero, he, hei, hform⟩ :=
      exists_height_coordinates_of_regular_normal hf.contMDiff N hN hnormal p hreg
    rcases hcases with hpos | hneg
    · exact ⟨e, σ, hσ, he0, hezero, he, hei, by simpa only [hpos] using hform⟩
    · refine ⟨e, fun i => -σ i, ?_, he0, hezero, he, hei, ?_⟩
      · intro i
        rcases hσ i with hi | hi <;> simp [hi]
      · intro x hx
        have h := hform x hx
        rw [hneg] at h
        change inner Real (-(v : E3)) (f (e x)) =
          inner Real (-(v : E3)) (f p) + ∑ i : Fin 2, σ i * x i ^ 2 at h
        simp only [inner_neg_left] at h
        rw [show (∑ i : Fin 2, -σ i * x i ^ 2) = -(∑ i : Fin 2, σ i * x i ^ 2) by
          simp only [neg_mul, Finset.sum_neg_distrib]]
        linarith

end Poincare.Manifold.Schoenflies
