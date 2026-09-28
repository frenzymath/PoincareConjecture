import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Basic








noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


lemma pullbackCoefficients_comp_of_eq (g : RiemannianMetric n M)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {e : EuclideanSpace ℝ (Fin n) → M}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e (f x))
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hmetric : h.euclideanCoefficients (f x) = g.pullbackCoefficients e (f x)) :
    h.pullbackCoefficients f x = g.pullbackCoefficients (e ∘ f) x := by
  ext u v
  change h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
    (mfderiv (𝓡 n) (𝓡 n) f x v) =
    g.inner (e (f x)) (mfderiv (𝓡 n) (𝓡 n) (e ∘ f) x u)
      (mfderiv (𝓡 n) (𝓡 n) (e ∘ f) x v)
  rw [mfderiv_comp x he hf]
  exact congrArg (fun B => B (mfderiv (𝓡 n) (𝓡 n) f x u)
    (mfderiv (𝓡 n) (𝓡 n) f x v)) hmetric



def UniformHarmonicLift.comp
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {r C H : ℝ} (F : UniformHarmonicLift h 0 r C H)
    (hr : 0 < r) (hC : 0 < C) (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {p : M}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U) (he0 : e 0 = p)
    (hmetric : ∀ y ∈ U, h.euclideanCoefficients y = g.pullbackCoefficients e y)
    (hmap : MapsTo F.e (Metric.ball 0 (2 * r)) U) :
    UniformHarmonicLift g p r C H := by
  have hsmooth := he.comp F.he hmap
  have hzero : (e ∘ F.e) 0 = p := by simp [F.he0, he0]
  have hpullback (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (2 * r)) :
      F.h.euclideanCoefficients x = g.pullbackCoefficients (e ∘ F.e) x := by
    rw [F.hpullback x hx]
    exact g.pullbackCoefficients_comp_of_eq
      ((he.contMDiffAt (hU.mem_nhds (hmap hx))).mdifferentiableAt (by simp))
      ((F.he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp))
      (hmetric _ (hmap hx))
  exact {
    e := e ∘ F.e
    h := F.h
    D' := F.D'
    he := hsmooth
    he0 := hzero
    hlocal := fun x hx => g.isInvertible_mfderiv_of_positive_pullback (by
      intro v hv
      rw [← hpullback x hx]
      exact F.h.pos x v hv)
    hpullback := hpullback
    helliptic := F.helliptic
    hderiv := F.hderiv
    hholder := F.hholder
    hharmonic := F.hharmonic
    hdist := fun x hx => g.edist_center_le_of_pullback_upper (by linarith)
      hsmooth hzero hC.le (fun y hy v => by
        rw [← hpullback y hy]
        exact (F.helliptic y hy v).2) hx }

end PoincareConjecture.RiemannianMetric
