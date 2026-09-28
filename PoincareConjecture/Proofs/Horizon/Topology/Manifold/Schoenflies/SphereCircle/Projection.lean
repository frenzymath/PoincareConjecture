import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sard.EqualDimension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Circle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function IsManifold
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩
private instance : Nonempty S2 := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

theorem dense_compl_range_smooth_circle_sphere
    {f : S1 -> S2} (hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f) :
    Dense (range f)ᶜ := by
  let L : E2 →L[Real] Real := EuclideanSpace.proj 0
  let g : Real -> S2 := f ∘ PoincareConjecture.unitCircleExp
  have hg : ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ g :=
    hf.comp PoincareConjecture.contMDiff_unitCircleExp
  have hG : ContMDiff (𝓡 2) (𝓡 2) ∞ (g ∘ L) := hg.comp L.contMDiff
  have hsing (x : E2) : ¬ Bijective (mfderiv (𝓡 2) (𝓡 2) (g ∘ L) x) := by
    intro hbij
    have hchain := mfderiv_comp x (hg.mdifferentiable (by simp) (L x))
      ((L.contMDiff (n := ∞)).mdifferentiable (by simp) x)
    rw [mfderiv_eq_fderiv, L.fderiv] at hchain
    have hLzero : L (EuclideanSpace.single (1 : Fin 2) (1 : Real)) = 0 := by
      change (EuclideanSpace.single (1 : Fin 2) (1 : Real)) (0 : Fin 2) = 0
      simp
    have heq : mfderiv (𝓡 2) (𝓡 2) (g ∘ L) x
        (EuclideanSpace.single (1 : Fin 2) (1 : Real)) = 0 := by
      rw [hchain]
      change mfderiv 𝓘(Real, Real) (𝓡 2) g (L x)
        (L (EuclideanSpace.single (1 : Fin 2) (1 : Real))) = 0
      rw [hLzero, map_zero]
    have hz := hbij.injective (heq.trans (map_zero _).symm)
    have hz' := congrArg (fun z : E2 => z (1 : Fin 2)) hz
    simp at hz'
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨p, hpU, hp⟩ := Poincare.Manifold.exists_regular_value_equal_dimension hG hU hUne
  refine ⟨p, hpU, ?_⟩
  rintro ⟨q, hq⟩
  obtain ⟨t, ht⟩ := PoincareConjecture.unitCircleExp_surjective q
  apply hsing (EuclideanSpace.single (0 : Fin 2) t)
  apply hp
  simpa [comp_apply, L, g, ht] using hq

theorem interior_range_smooth_circle_sphere_eq_empty
    {f : S1 -> S2} (hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f) :
    interior (range f) = ∅ :=
  interior_eq_empty_iff_dense_compl.mpr (dense_compl_range_smooth_circle_sphere hf)

theorem exists_point_not_mem_range_smooth_circle_sphere
    {f : S1 -> S2} (hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f) :
    ∃ p : S2, p ∉ range f :=
  (dense_compl_range_smooth_circle_sphere hf).nonempty

theorem isSmoothEmbedding_stereographic_circle_of_injective_mfderiv
    {f : S1 -> S2} (hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f)
    (hfi : Injective f) (hfd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) f q))
    {p : S2} (hp : p ∉ range f) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (stereographic' 2 p ∘ f) := by
  let e := stereographic' 2 p
  have he : e ∈ maximalAtlas (𝓡 2) ∞ S2 :=
    IsManifold.subset_maximalAtlas ⟨p, rfl⟩
  have hsource (q : S1) : f q ∈ e.source := by
    rw [stereographic'_source]
    intro heq
    exact hp ⟨q, heq⟩
  have hs : ContMDiff (𝓡 1) (𝓡 2) ∞ (e ∘ f) := by
    intro q
    exact (contMDiffAt_of_mem_maximalAtlas he (hsource q)).comp q (hf q)
  have hinj : Injective (e ∘ f) := by
    intro q q' hqq'
    exact hfi (e.injOn (hsource q) (hsource q') hqq')
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv hs hinj
  intro q
  have hem : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  rw [mfderiv_comp q (hem.mdifferentiableAt (hsource q))
    (hf.mdifferentiable (by simp) q)]
  exact (hem.mfderiv_injective (hsource q)).comp (hfd q)

theorem isSmoothEmbedding_stereographic_circle
    {f : S1 -> S2} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f)
    {p : S2} (hp : p ∉ range f) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (stereographic' 2 p ∘ f) :=
  isSmoothEmbedding_stereographic_circle_of_injective_mfderiv hf.contMDiff
    hf.isEmbedding.injective (fun q =>
      (hf.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp)) hp

theorem exists_stereographic_planar_circle
    {f : S1 -> S2} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f) :
    ∃ (p : S2) (γ : S1 -> E2), p ∉ range f ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ ∧
      ContMDiff (𝓡 2) (𝓡 2) ∞ (stereographic' 2 p).symm ∧
      (∀ q, γ q = stereographic' 2 p (f q)) ∧
      ∀ q, (stereographic' 2 p).symm (γ q) = f q := by
  obtain ⟨p, hp⟩ := exists_point_not_mem_range_smooth_circle_sphere hf.contMDiff
  have he : stereographic' 2 p ∈ maximalAtlas (𝓡 2) ∞ S2 :=
    IsManifold.subset_maximalAtlas ⟨p, rfl⟩
  refine ⟨p, stereographic' 2 p ∘ f, hp, isSmoothEmbedding_stereographic_circle hf hp,
    ?_, fun _ => rfl, ?_⟩
  · rw [← contMDiffOn_univ]
    simpa only [stereographic'_target] using contMDiffOn_symm_of_mem_maximalAtlas he
  · intro q
    apply (stereographic' 2 p).left_inv
    rw [stereographic'_source]
    intro heq
    exact hp ⟨q, heq⟩

end Poincare.Manifold.Schoenflies
