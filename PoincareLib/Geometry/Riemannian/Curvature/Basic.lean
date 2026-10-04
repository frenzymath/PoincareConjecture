import PoincareLib.Geometry.Riemannian.Connection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch01/Curvature.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Curvature evaluated from the chosen connection

These expressions follow Morgan-Tian, printed pp. 5-7. The fixed local
extensions are retained throughout each iterated derivative. Local regularity,
extension independence, tensoriality, and basis independence remain separate
supporting theorems; see reviews/contracts/curvature-v1.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RiemannianMetric

/-- A pointwise orthonormal basis for the chosen metric; no smooth frame is asserted. -/
noncomputable def orthonormalBasis (g : RiemannianMetric n M) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)))
      ℝ (TangentSpace (𝓡 n) x) :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x)

end RiemannianMetric

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

/-- The curvature commutator on sections; its geometric use requires regular germs. -/
noncomputable def curvatureOnFields (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    TangentSpace (𝓡 n) x :=
  D.connection (fun y ↦ D.connection Z y (Y y)) x (X x) -
    D.connection (fun y ↦ D.connection Z y (X y)) x (Y x) -
    D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x)

/-- Pointwise `(1,3)` curvature evaluated using fixed locally smooth extensions. -/
noncomputable def curvature (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) : TangentSpace (𝓡 n) x :=
  D.curvatureOnFields
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x

/-- Four-covariant curvature with the book's last-slot interchange: `g(R(u,v)z,w)`. -/
noncomputable def curvatureTensor (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) : ℝ :=
  g.inner x (D.curvature x u v z) w

/-- Ricci curvature contracted in a pointwise basis orthonormal for the chosen metric. -/
noncomputable def ricci (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, D.curvatureTensor x u (b i) v (b i)

/-- Scalar curvature, the metric trace of the Ricci evaluations. -/
noncomputable def scalarCurvature (D : LeviCivitaData g) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, D.ricci x (b i) (b i)

/-- Sectional curvature for an independent pair, totalized as zero at zero Gram determinant. -/
noncomputable def sectionalCurvature (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  D.curvatureTensor x u v u v /
    (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)

/-- The full four-covariant Hilbert-Schmidt norm, distinct from a curvature-operator norm. -/
noncomputable def curvatureTensorNorm (D : LeviCivitaData g) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2)

end LeviCivitaData

end PoincareMT
