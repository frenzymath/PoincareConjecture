import PoincareLib.Geometry.Riemannian.Connection.LocalRegularity

/-!
# Uniqueness of the Levi-Civita connection on differentiable germs

The metric and torsion conditions determine a retained connection on locally
differentiable sections. No equality on arbitrary total sections is asserted.
This is a prerequisite for identifying curvature after coordinate changes.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Two metric-compatible torsion-free connections agree on a differentiable
section at the point of differentiability. -/
theorem connection_eq_of_mdifferentiableAt (D D' : LeviCivitaData g)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) (v : TangentSpace (𝓡 n) x) :
    D.connection Y x v = D'.connection Y x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  have hX := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  have h₁ := D.koszul_identity hX hY hZ
  have h₂ := D'.koszul_identity hX hY hZ
  simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at h₁ h₂
  change g.inner x (D.connection Y x v) w = g.inner x (D'.connection Y x v) w
  linarith

/-- The iterated covariant derivative of locally smooth fields is independent
of the chosen compatible torsion-free connection. -/
theorem connection_covariantDerivativeOnFields_eq (D D' : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (v : TangentSpace (𝓡 n) x) :
    D.connection (D.covariantDerivativeOnFields X Y) x v =
      D'.connection (D'.covariantDerivativeOnFields X Y) x v := by
  have hD := D.contMDiffAt_covariantDerivativeOnFields hX hY
  have hD' := D'.contMDiffAt_covariantDerivativeOnFields hX hY
  have heq : D.covariantDerivativeOnFields X Y =ᶠ[𝓝 x]
      D'.covariantDerivativeOnFields X Y := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hY] with y hy
    exact D.connection_eq_of_mdifferentiableAt D' hy (X y)
  have hconn := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hD.mdifferentiableAt (by simp)) (hD'.mdifferentiableAt (by simp)) (by simp) heq
  exact (congrArg (fun L ↦ L v) hconn).trans
    (D.connection_eq_of_mdifferentiableAt D' (hD'.mdifferentiableAt (by simp)) v)

/-- Curvature on locally smooth fields depends only on the metric. -/
theorem curvatureOnFields_eq_of_contMDiffAt (D D' : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    D.curvatureOnFields X Y Z x = D'.curvatureOnFields X Y Z x := by
  change D.connection (D.covariantDerivativeOnFields Y Z) x (X x) -
      D.connection (D.covariantDerivativeOnFields X Z) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x) = _
  rw [D.connection_covariantDerivativeOnFields_eq D' hY hZ,
    D.connection_covariantDerivativeOnFields_eq D' hX hZ,
    D.connection_eq_of_mdifferentiableAt D' (hZ.mdifferentiableAt (by simp))]
  rfl

/-- The frozen fixed-extension curvature is independent of the retained
compatible torsion-free connection. -/
theorem curvature_eq (D D' : LeviCivitaData g) (x : M)
    (v w z : TangentSpace (𝓡 n) x) :
    D.curvature x v w z = D'.curvature x v w z := by
  exact D.curvatureOnFields_eq_of_contMDiffAt D'
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) z)

/-- The four-covariant curvature tensor is independent of the retained connection. -/
theorem curvatureTensor_eq (D D' : LeviCivitaData g) (x : M)
    (v w z u : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v w z u = D'.curvatureTensor x v w z u := by
  simp only [curvatureTensor, D.curvature_eq D']

/-- The frozen Hilbert-Schmidt curvature norm is independent of the retained connection. -/
theorem curvatureTensorNorm_eq (D D' : LeviCivitaData g) (x : M) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm x := by
  simp only [curvatureTensorNorm, D.curvatureTensor_eq D']

/-- Scalar curvature is independent of the retained compatible connection. -/
theorem scalarCurvature_eq (D D' : LeviCivitaData g) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  simp only [scalarCurvature, ricci, D.curvatureTensor_eq D']

end PoincareMT.LeviCivitaData
