import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.MetricSeparation
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.MFDeriv.Zero
import Mathlib.Analysis.Normed.Module.Connected







set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem involution_preserves_tangent_kernels (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    ∀ p : q.product.surface × ℝ, ∀ v : TangentSpace (𝓡 3) p,
      (q.product.tangent_surface_component p v = 0 →
        q.product.tangent_surface_component (q.involution p)
          (mfderiv (𝓡 3) (𝓡 3) q.involution p v) = 0) ∧
      (q.product.tangent_line_component p v = 0 →
        q.product.tangent_line_component (q.involution p)
          (mfderiv (𝓡 3) (𝓡 3) q.involution p v) = 0) := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  intro p v
  obtain ⟨hs, hl⟩ := q.involution_preserves_tangent_forms p v v
  constructor
  · intro hv
    rw [hv] at hs
    simp only [map_zero] at hs
    by_contra hn
    exact (q.product.surface_metric (-1)).pos _ _ hn |>.ne' hs.symm
  · intro hv
    rw [hv, zero_mul] at hl
    exact mul_self_eq_zero.mp hl.symm


theorem involution_cross_mfderiv_eq_zero (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    (∀ s : q.product.surface, ∀ z : ℝ,
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun a => (q.involution (s, a)).1) z = 0) ∧
    (∀ z : ℝ, ∀ s : q.product.surface,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun a => (q.involution (a, z)).2) s = 0) := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  have hfst : ContMDiff (𝓡 3) (𝓡 2) ∞
      (Prod.fst : q.product.surface × ℝ → q.product.surface) :=
    q.product.product_smooth_to_canonical.fst
  have hsnd : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : q.product.surface × ℝ → ℝ) :=
    q.product.product_smooth_to_canonical.snd
  constructor
  · intro s z
    have hi : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞
        (fun a : ℝ => (s, a)) :=
      q.product.product_smooth_from_canonical.comp (contMDiff_const.prodMk contMDiff_id)
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      (Prod.fst ∘ (q.involution ∘ fun a : ℝ => (s, a))) z = 0
    rw [mfderiv_comp z (hfst.mdifferentiable (by simp) _)
      ((q.involution_smooth.comp hi).mdifferentiable (by simp) z),
      mfderiv_comp z (q.involution_smooth.mdifferentiable (by simp) _)
        (hi.mdifferentiable (by simp) z)]
    apply ContinuousLinearMap.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 2) Prod.fst (q.involution (s, z)) _ = 0
    rw [← q.product.tangent_surface_component_eq]
    apply (q.involution_preserves_tangent_kernels (s, z) _).1
    rw [q.product.tangent_surface_component_eq]
    have hc := congrArg (fun L => L v)
      (mfderiv_comp z (hfst.mdifferentiable (by simp) _)
        (hi.mdifferentiable (by simp) z))
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun _ : ℝ => s) z) v = _ at hc
    rw [mfderiv_const] at hc
    exact hc.symm
  · intro z s
    have hi : ContMDiff (𝓡 2) (𝓡 3) ∞
        (fun a : q.product.surface => (a, z)) :=
      q.product.product_smooth_from_canonical.comp (contMDiff_id.prodMk contMDiff_const)
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (Prod.snd ∘ (q.involution ∘ fun a : q.product.surface => (a, z))) s = 0
    rw [mfderiv_comp s (hsnd.mdifferentiable (by simp) _)
      ((q.involution_smooth.comp hi).mdifferentiable (by simp) s),
      mfderiv_comp s (q.involution_smooth.mdifferentiable (by simp) _)
        (hi.mdifferentiable (by simp) s)]
    apply ContinuousLinearMap.ext
    intro v
    change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) Prod.snd (q.involution (s, z)) _ = 0
    rw [← q.product.tangent_line_component_eq]
    apply (q.involution_preserves_tangent_kernels (s, z) _).2
    rw [q.product.tangent_line_component_eq]
    have hc := congrArg (fun L => L v)
      (mfderiv_comp s (hsnd.mdifferentiable (by simp) _)
        (hi.mdifferentiable (by simp) s))
    change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun _ : q.product.surface => z) s) v = _ at hc
    rw [mfderiv_const] at hc
    exact hc.symm



theorem exists_smooth_factorization (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    ∃ f : q.product.surface → q.product.surface, ∃ g : ℝ → ℝ,
      ContMDiff (𝓡 2) (𝓡 2) ∞ f ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g ∧
      Function.Involutive f ∧ Function.Involutive g ∧
      ∀ s z, q.involution (s, z) = (f s, g z) := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  letI : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  letI : ConnectedSpace q.product.surface :=
    q.product.surface_sphere.toHomeomorph.connectedSpace_iff.mpr inferInstance
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let s₀ : q.product.surface := Classical.arbitrary _
  have hfst : ContMDiff (𝓡 3) (𝓡 2) ∞
      (Prod.fst : q.product.surface × ℝ → q.product.surface) :=
    q.product.product_smooth_to_canonical.fst
  have hsnd : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : q.product.surface × ℝ → ℝ) :=
    q.product.product_smooth_to_canonical.snd
  have hs : ∀ z : ℝ, ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun a : q.product.surface => (a, z)) := fun z =>
    q.product.product_smooth_from_canonical.comp (contMDiff_id.prodMk contMDiff_const)
  have hl : ∀ s : q.product.surface, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun a : ℝ => (s, a)) := fun s =>
    q.product.product_smooth_from_canonical.comp (contMDiff_const.prodMk contMDiff_id)
  have he : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun s : q.product.surface => (q.product.surface_sphere s).1) :=
    contMDiff_coe_sphere.comp q.product.surface_sphere.contMDiff
  have hfirst : ∀ s z, (q.involution (s, z)).1 = (q.involution (s, 0)).1 := by
    intro s z
    apply q.product.surface_sphere.injective
    apply Subtype.ext
    have hh : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞
        (fun a : ℝ => (q.involution (s, a)).1) :=
      hfst.comp (q.involution_smooth.comp (hl s))
    apply eq_of_mfderiv_eq_zero ((he.comp hh).mdifferentiable (by simp)) _ z 0
    intro a
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      ((fun b : q.product.surface => (q.product.surface_sphere b).1) ∘
        (fun b : ℝ => (q.involution (s, b)).1)) a = 0
    rw [mfderiv_comp a (he.mdifferentiable (by simp) _) (hh.mdifferentiable (by simp) a),
      q.involution_cross_mfderiv_eq_zero.1]
    apply ContinuousLinearMap.ext
    intro v
    change mfderiv (𝓡 2) (𝓡 3)
      (fun b : q.product.surface => (q.product.surface_sphere b).1)
      (q.involution (s, a)).1 0 = 0
    exact map_zero _
  have hsecond : ∀ s z, (q.involution (s, z)).2 = (q.involution (s₀, z)).2 := by
    intro s z
    apply eq_of_mfderiv_eq_zero
      ((hsnd.comp (q.involution_smooth.comp (hs z))).mdifferentiable (by simp))
      (q.involution_cross_mfderiv_eq_zero.2 z) s s₀
  let f : q.product.surface → q.product.surface := fun s => (q.involution (s, 0)).1
  let g : ℝ → ℝ := fun z => (q.involution (s₀, z)).2
  have hfactor : ∀ s z, q.involution (s, z) = (f s, g z) := by
    intro s z
    exact Prod.ext (hfirst s z) (hsecond s z)
  refine ⟨f, g, hfst.comp (q.involution_smooth.comp (hs 0)),
    hsnd.comp (q.involution_smooth.comp (hl s₀)), ?_, ?_, hfactor⟩
  · intro s
    have h := congrArg Prod.fst (q.involution_involutive (s, 0))
    simpa only [hfactor] using h
  · intro z
    have h := congrArg Prod.snd (q.involution_involutive (s₀, z))
    simpa only [hfactor] using h

end PoincareConjecture.QuotientSphereLineCertificate
