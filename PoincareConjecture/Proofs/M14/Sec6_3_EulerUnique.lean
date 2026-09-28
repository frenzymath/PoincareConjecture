import PoincareConjecture.Proofs.M14.Sec6_3_EulerLocalUnique
import PoincareConjecture.Proofs.M14.Mathlib.FiberBundleHausdorff
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem squareRootEuler_unique
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T τ₁ τ₂ σ₁ σ₂ : ℝ} {x₁ y₁ x₂ y₂ : G.Point}
    {p₁ : M14BackwardPath G T τ₁ τ₂ x₁ y₁} {p₂ : M14BackwardPath G T σ₁ σ₂ x₂ y₂}
    (R₁ : M14SquareRootPath G p₁) (R₂ : M14SquareRootPath G p₂)
    {a c s₀ : ℝ} (hac : a < c)
    (hsub₁ : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    (hsub₂ : Icc a c ⊆ M14SqrtParameterInterval σ₁ σ₂)
    (E₁ : M14PullbackExtension G R₁.curve (M14SqrtParameterInterval τ₁ τ₂)
      R₁.horizontal_velocity)
    (E₂ : M14PullbackExtension G R₂.curve (M14SqrtParameterInterval σ₁ σ₂)
      R₂.horizontal_velocity)
    (heuler₁ : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R₁.curve s),
      M14SquareRootEulerResidual G R₁ E₁ s Z = 0)
    (heuler₂ : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R₂.curve s),
      M14SquareRootEulerResidual G R₂ E₂ s Z = 0)
    (hs₀ : s₀ ∈ Icc a c) (heq : R₁.curve s₀ = R₂.curve s₀)
    (hvel : HEq (R₁.horizontal_velocity s₀) (R₂.horizontal_velocity s₀)) :
    ∀ s ∈ Icc a c,
      R₁.curve s = R₂.curve s ∧ HEq (R₁.horizontal_velocity s) (R₂.horizontal_velocity s) := by
  let f := fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
    (E := G.Horizontal) (R₁.curve s) (R₁.horizontal_velocity s)
  let g := fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
    (E := G.Horizontal) (R₂.curve s) (R₂.horizontal_velocity s)
  have hfc : ContinuousOn f (Icc a c) :=
    ((squareRoot_horizontalVelocity_smooth R₁).mono hsub₁).continuousOn
  have hgc : ContinuousOn g (Icc a c) :=
    ((squareRoot_horizontalVelocity_smooth R₂).mono hsub₂).continuousOn
  let : T2Space (Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal) :=
    fiberBundle_totalSpace_t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal
  let : PreconnectedSpace (Icc a c) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let A : Set (Icc a c) := {s | f s = g s}
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    have hstate := Bundle.TotalSpace.ext_iff.mp hs
    have hlocal := squareRootEuler_eventuallyEqWithin hM04 hM12 R₁ R₂ hac hsub₁ hsub₂
      E₁ E₂ heuler₁ heuler₂ s.property hstate.1 hstate.2
    apply (eventually_nhds_subtype_iff (Icc a c) s (fun t => f t = g t)).mpr
    filter_upwards [hlocal] with t ht
    exact Bundle.TotalSpace.ext ht.1 ht.2
  have hAll : A = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩
    ⟨⟨s₀, hs₀⟩, Bundle.TotalSpace.ext heq hvel⟩
  intro s hs
  have hmem : (⟨s, hs⟩ : Icc a c) ∈ A := by rw [hAll]; trivial
  exact Bundle.TotalSpace.ext_iff.mp hmem

end PoincareConjecture.M14
