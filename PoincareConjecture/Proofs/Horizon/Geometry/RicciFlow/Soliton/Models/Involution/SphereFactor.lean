import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.FactorMetrics
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereIsometry

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

open Poincare.Geometry.Riemannian.SpaceForm

namespace SphereLineProductData

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]

theorem surface_sphere_scaled_inner (d : SphereLineProductData (P := P)) :
    letI := d.surface_topology
    letI := d.surface_charted
    letI := d.surface_manifold
    ∀ p : d.surface, ∀ v w : TangentSpace (𝓡 2) p,
      (d.surface_metric (-1)).inner p v w =
        2 * (roundSphereMetric 2).inner (d.surface_sphere p)
          (mfderiv (𝓡 2) (𝓡 2) d.surface_sphere p v)
          (mfderiv (𝓡 2) (𝓡 2) d.surface_sphere p w) := by
  letI := d.surface_topology
  letI := d.surface_charted
  letI := d.surface_manifold
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  intro p v w
  rw [d.surface_inner_round (-1) (by norm_num), roundSphereMetric_inner,
    RiemannianMetric.euclideanMetric_inner]
  have hd := mfderiv_comp p
    ((contMDiff_coe_sphere (m := ∞) (n := 2)).mdifferentiable (by simp) _)
    (d.surface_sphere.contMDiff.mdifferentiable (by simp) p)
  change mfderiv (𝓡 2) (𝓡 3) (fun s : d.surface => (d.surface_sphere s).1) p = _ at hd
  rw [hd]
  norm_num

theorem sphere_conjugate_preserves_metric (d : SphereLineProductData (P := P)) :
    letI := d.surface_topology
    letI := d.surface_charted
    letI := d.surface_manifold
    ∀ e : Diffeomorph (𝓡 2) (𝓡 2) d.surface d.surface ∞,
      (∀ p : d.surface, ∀ v w : TangentSpace (𝓡 2) p,
        (d.surface_metric (-1)).inner p v w =
          (d.surface_metric (-1)).inner (e p)
            (mfderiv (𝓡 2) (𝓡 2) e p v) (mfderiv (𝓡 2) (𝓡 2) e p w)) →
      let k := (d.surface_sphere.symm.trans e).trans d.surface_sphere
      ∀ x : UnitTwoSphere, ∀ v w : TangentSpace (𝓡 2) x,
        (roundSphereMetric 2).inner x v w =
          (roundSphereMetric 2).inner (k x)
            (mfderiv (𝓡 2) (𝓡 2) k x v) (mfderiv (𝓡 2) (𝓡 2) k x w) := by
  letI := d.surface_topology
  letI := d.surface_charted
  letI := d.surface_manifold
  intro e he k x v w
  let a := d.surface_sphere
  have hsrc (v : TangentSpace (𝓡 2) x) :
      mfderiv (𝓡 2) (𝓡 2) a (a.symm x)
        (mfderiv (𝓡 2) (𝓡 2) a.symm x v) = v := by
    have h := mfderiv_comp x (a.contMDiff.mdifferentiable (by simp) _)
      (a.symm.contMDiff.mdifferentiable (by simp) x)
    have hcomp : a ∘ a.symm = id := by funext y; exact a.apply_symm_apply y
    rw [hcomp, mfderiv_id] at h
    exact congrArg (fun L => L v) h.symm
  have htgt (v : TangentSpace (𝓡 2) x) :
      mfderiv (𝓡 2) (𝓡 2) a (e (a.symm x))
        (mfderiv (𝓡 2) (𝓡 2) e (a.symm x)
          (mfderiv (𝓡 2) (𝓡 2) a.symm x v)) =
        mfderiv (𝓡 2) (𝓡 2) k x v := by
    have h := mfderiv_comp x (a.contMDiff.mdifferentiable (by simp) _)
      ((e.contMDiff.comp a.symm.contMDiff).mdifferentiable (by simp) x)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _)
      (a.symm.contMDiff.mdifferentiable (by simp) x)] at h
    exact congrArg (fun L => L v) h.symm
  have h := he (a.symm x) (mfderiv (𝓡 2) (𝓡 2) a.symm x v)
    (mfderiv (𝓡 2) (𝓡 2) a.symm x w)
  rw [d.surface_sphere_scaled_inner, d.surface_sphere_scaled_inner,
    hsrc, hsrc, htgt, htgt] at h
  change 2 * (roundSphereMetric 2).inner (a (a.symm x)) v w =
    2 * (roundSphereMetric 2).inner (k x)
      (mfderiv (𝓡 2) (𝓡 2) k x v) (mfderiv (𝓡 2) (𝓡 2) k x w) at h
  rw [a.apply_symm_apply] at h
  linarith

end SphereLineProductData

namespace QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem factor_sphere_isometry (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    ∀ (f : q.product.surface → q.product.surface) (g : ℝ → ℝ),
      ContMDiff (𝓡 2) (𝓡 2) ∞ f → Function.Involutive f →
      (∀ s z, q.involution (s, z) = (f s, g z)) →
      Isometry (fun x : UnitTwoSphere =>
        q.product.surface_sphere (f (q.product.surface_sphere.symm x))) := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  intro f g hf hfi hfactor
  let e : Diffeomorph (𝓡 2) (𝓡 2) q.product.surface q.product.surface ∞ :=
    { toFun := f
      invFun := f
      left_inv := hfi
      right_inv := hfi
      contMDiff_toFun := hf
      contMDiff_invFun := hf }
  exact roundSphere_diffeomorph_isometry (by norm_num)
    ((q.product.surface_sphere.symm.trans e).trans q.product.surface_sphere)
    (q.product.sphere_conjugate_preserves_metric e (q.factor_surface_metric f g hfactor))

end QuotientSphereLineCertificate

end PoincareConjecture
