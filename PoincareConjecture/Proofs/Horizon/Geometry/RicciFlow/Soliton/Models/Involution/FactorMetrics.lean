import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.MetricSeparation
import Mathlib.Analysis.Calculus.MeanValue

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

theorem factor_surface_metric (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    ∀ (f : q.product.surface → q.product.surface) (g : ℝ → ℝ),
      (∀ s z, q.involution (s, z) = (f s, g z)) →
      ∀ s : q.product.surface, ∀ v w : TangentSpace (𝓡 2) s,
        (q.product.surface_metric (-1)).inner s v w =
          (q.product.surface_metric (-1)).inner (f s)
            (mfderiv (𝓡 2) (𝓡 2) f s v) (mfderiv (𝓡 2) (𝓡 2) f s w) := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  intro f g hfactor s v w
  let j : q.product.surface → q.product.surface × ℝ := fun a => (a, 0)
  have hj : ContMDiff (𝓡 2) (𝓡 3) ∞ j :=
    q.product.product_smooth_from_canonical.comp (contMDiff_id.prodMk contMDiff_const)
  have hfst : ContMDiff (𝓡 3) (𝓡 2) ∞
      (Prod.fst : q.product.surface × ℝ → q.product.surface) :=
    q.product.product_smooth_to_canonical.fst
  have hsrc (v : TangentSpace (𝓡 2) s) :
      q.product.tangent_surface_component (j s) (mfderiv (𝓡 2) (𝓡 3) j s v) = v := by
    rw [q.product.tangent_surface_component_eq]
    have h := mfderiv_comp s (hfst.mdifferentiable (by simp) _) (hj.mdifferentiable (by simp) s)
    change mfderiv (𝓡 2) (𝓡 2) id s = _ at h
    rw [mfderiv_id] at h
    exact congrArg (fun L => L v) h.symm
  have htgt (v : TangentSpace (𝓡 2) s) :
      q.product.tangent_surface_component (q.involution (j s))
        (mfderiv (𝓡 3) (𝓡 3) q.involution (j s) (mfderiv (𝓡 2) (𝓡 3) j s v)) =
          mfderiv (𝓡 2) (𝓡 2) f s v := by
    rw [q.product.tangent_surface_component_eq]
    have h := mfderiv_comp s (hfst.mdifferentiable (by simp) _)
      ((q.involution_smooth.comp hj).mdifferentiable (by simp) s)
    rw [mfderiv_comp s (q.involution_smooth.mdifferentiable (by simp) _)
      (hj.mdifferentiable (by simp) s)] at h
    have heq : Prod.fst ∘ (q.involution ∘ j) = f := by
      funext a
      exact congrArg Prod.fst (hfactor a 0)
    rw [heq] at h
    exact congrArg (fun L => L v) h.symm
  have h := (q.involution_preserves_tangent_forms (j s)
    (mfderiv (𝓡 2) (𝓡 3) j s v) (mfderiv (𝓡 2) (𝓡 3) j s w)).1
  rw [hsrc, hsrc, htgt, htgt] at h
  have hp : (q.involution (j s)).1 = f s := congrArg Prod.fst (hfactor s 0)
  change (q.product.surface_metric (-1)).inner s v w =
    (q.product.surface_metric (-1)).inner (q.involution (j s)).1
      (mfderiv (𝓡 2) (𝓡 2) f s v) (mfderiv (𝓡 2) (𝓡 2) f s w) at h
  rw [hp] at h
  exact h

theorem factor_line_deriv_sq (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    ∀ (f : q.product.surface → q.product.surface) (g : ℝ → ℝ),
      (∀ s z, q.involution (s, z) = (f s, g z)) →
      ∀ _s : q.product.surface, ∀ z : ℝ, deriv g z ^ 2 = 1 := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  intro f g hfactor s z
  let j : ℝ → q.product.surface × ℝ := fun a => (s, a)
  have hj : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ j :=
    q.product.product_smooth_from_canonical.comp (contMDiff_const.prodMk contMDiff_id)
  have hsnd : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : q.product.surface × ℝ → ℝ) :=
    q.product.product_smooth_to_canonical.snd
  have hsrc : q.product.tangent_line_component (j z)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) j z 1) = 1 := by
    rw [q.product.tangent_line_component_eq]
    have h := mfderiv_comp z (hsnd.mdifferentiable (by simp) _) (hj.mdifferentiable (by simp) z)
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id z = _ at h
    rw [mfderiv_id] at h
    exact congrArg (fun L => L 1) h.symm
  have htgt : q.product.tangent_line_component (q.involution (j z))
      (mfderiv (𝓡 3) (𝓡 3) q.involution (j z) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) j z 1)) =
        deriv g z := by
    rw [q.product.tangent_line_component_eq]
    have h := mfderiv_comp z (hsnd.mdifferentiable (by simp) _)
      ((q.involution_smooth.comp hj).mdifferentiable (by simp) z)
    rw [mfderiv_comp z (q.involution_smooth.mdifferentiable (by simp) _)
      (hj.mdifferentiable (by simp) z)] at h
    have heq : Prod.snd ∘ (q.involution ∘ j) = g := by
      funext a
      exact congrArg Prod.snd (hfactor s a)
    rw [heq, mfderiv_eq_fderiv] at h
    exact congrArg (fun L => L 1) h.symm
  have h := (q.involution_preserves_tangent_forms (j z)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) j z 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) j z 1)).2
  rw [hsrc, htgt] at h
  nlinarith

theorem real_isometry_of_involutive_deriv_sq {g : ℝ → ℝ}
    (hg : Differentiable ℝ g) (hi : Function.Involutive g)
    (hd : ∀ z, deriv g z ^ 2 = 1) : Isometry g := by
  have hl : LipschitzWith 1 g := lipschitzWith_of_nnnorm_deriv_le hg fun z => by
    change |deriv g z| ≤ (1 : ℝ)
    rcases sq_eq_one_iff.mp (hd z) with h | h <;> simp [h]
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa using hl.dist_le_mul x y
  · simpa only [hi x, hi y, NNReal.coe_one, one_mul] using hl.dist_le_mul (g x) (g y)

end PoincareConjecture.QuotientSphereLineCertificate
