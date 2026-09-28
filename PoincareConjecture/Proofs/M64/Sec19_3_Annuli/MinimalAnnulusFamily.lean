import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ElementaryFields
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ForwardMinimalCompetitor
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusInterface

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

structure M64MinimalAnnulusFamily
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (c0 c1 : ℝ → ℝ → P.charts.Point) (rate : ℝ → ℝ) where
  data : ∀ t ∈ Set.Icc a b,
    M64MinimalAnnulusData
      (g := P.flow.metric t)
      (c0 := fun x => c0 x t) (c1 := fun x => c1 x t)
  competitor : ∀ t ∈ Set.Ico a b, ∀ eta : ℝ, 0 < eta →
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ m64FlowAnnulusArea P c0 c1 t + h * (rate t + eta)

theorem m64AnnulusFlow_forward_of_minimal_family
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point} {rate : ℝ → ℝ}
    (E : M64MinimalAnnulusFamily P c0 c1 rate) :
    ∀ t ∈ Set.Ico a b,
      AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1) (rate t) t := by
  intro t ht
  have htcc : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
  let A := E.data t htcc
  have hmin : A.annulus.area = m64FlowAnnulusArea P c0 c1 t := by
    simpa only [A, m64FlowAnnulusArea] using A.area_minimal
  apply m64AnnulusForward_of_minimal_competitors A.annulus hmin
  intro eta heta
  simpa only [hmin] using E.competitor t ht eta heta

theorem m64AnnulusFlow_elementary_fields_of_minimal_family
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point} {rate : ℝ → ℝ}
    (E : M64MinimalAnnulusFamily P c0 c1 rate) :
    (∀ t ∈ Set.Icc a b,
      Nonempty (M64Annulus (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      BddBelow (m64AnnulusAreaRange (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      0 ≤ m64FlowAnnulusArea P c0 c1 t) := by
  apply m64AnnulusFlow_elementary_fields
  intro t ht
  exact ⟨(E.data t ht).annulus⟩

theorem m64AnnulusFlow_elementary_fields_of_minimal_data
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (data : ∀ t ∈ Set.Icc a b,
      M64MinimalAnnulusData
        (g := P.flow.metric t)
        (c0 := fun x => c0 x t) (c1 := fun x => c1 x t)) :
    (∀ t ∈ Set.Icc a b,
      Nonempty (M64Annulus (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      BddBelow (m64AnnulusAreaRange (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      0 ≤ m64FlowAnnulusArea P c0 c1 t) := by
  apply m64AnnulusFlow_elementary_fields
  intro t ht
  exact ⟨(data t ht).annulus⟩

end PoincareConjecture
