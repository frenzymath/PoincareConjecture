import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.OrientedWindows
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.PeriodicRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Periodic.WindowSegments

set_option autoImplicit false
open Set Geometry
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76.PeriodicSquare

theorem exists_marked_product_of_commensurable_boundary_tori_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R S₀ S₁ : Set X}
    (hI : IsPLIrreducible e R) (hR : IsCompact R) (hconn : IsConnected R)
    (O : LocalOrientation X)
    (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁) (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X) = S₁)
    (hinj₀ : Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset)) x₀))
    (hinj₁ : Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset)) x₁))
    (k : Path
      ((ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset)) x₀)
      ((ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset)) x₁))
    (hcomm : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans hI.1.closed.frontier_subset)) x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
        (FundamentalGroup.map
          (ContinuousMap.inclusion (hS₁.trans hI.1.closed.frontier_subset)) x₁)).range))
    {p₀ p₁ : ℝ} [Fact (0 < p₀)] [Fact (0 < p₁)]
    (h₀ : (AddCircle p₀ × AddCircle p₀) ≃ₜ S₀)
    (h₁ : (AddCircle p₁ × AddCircle p₁) ≃ₜ S₁)
    (v₀ v₁ : ℝ × ℝ → X)
    (hv₀ : PolyhedralPLInCharts e v₀ (squareCarrier p₀))
    (hv₁ : PolyhedralPLInCharts e v₁ (squareCarrier p₁))
    (hvvalue₀ : ∀ z : Square p₀, v₀ (z.1, z.2) = (h₀ (projection p₀ z) : X))
    (hvvalue₁ : ∀ z : Square p₁, v₁ (z.1, z.2) = (h₁ (projection p₁ z) : X)) :
    ∃ H : (S₀ × unitInterval) ≃ₜ R,
      (∀ x, (H (x, ⟨0, by norm_num⟩) : X) = x) ∧
      range (fun x => (H (x, ⟨1, by norm_num⟩) : X)) = S₁ ∧
      (∀ x t, (H (x, t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      ∃ (s : Finset R) (G : X → (s → ℝ × (Fin 3 → ℝ)))
        (HG : ((G '' S₀) ×ˢ Set.Icc (0 : ℝ) 1) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : S₀) (t : unitInterval),
          (HG ⟨(G x, t), ⟨mem_image_of_mem G x.property, t.property⟩⟩ :
            s → ℝ × (Fin 3 → ℝ)) = G (H (x, t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X)
          (b : (s → ℝ × (Fin 3 → ℝ)) →ᴬ[ℝ] (Fin 3 → ℝ)),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  obtain ⟨s₀, s₁, K₀, K₁, F₀, F₁, H₀, H₁, M₀, M₁, g, q, r,
      hK₀, hK₁, hF₀, hF₁, hFval₀, hFval₁, hvalue₀, hvalue₁, hg, hr⟩ :=
    hI.1.exists_original_spanning_pair_with_periodic_rims O hR hconn hS₀ hS₁ hdis
      x₀ x₁ hcomponent₀ hcomponent₁ hinj₀ k hcomm h₀ h₁ v₀ v₁ hv₀ hv₁ hvvalue₀ hvvalue₁
  let W := Icc (-p₁) (2 * p₁) ×ˢ Icc (-p₁) (2 * p₁)
  have hW : IsCompact W := isCompact_Icc.prod isCompact_Icc
  obtain ⟨I, hI', a, b, _, hselfA, hwindowA⟩ :=
    exists_finite_periodic_window_segments (Fact.out : 0 < p₁)
      (hr false).1 (hr false).2.2.1 hW
  obtain ⟨J, hJ', c, d, hcd, hselfB, hwindowB⟩ :=
    exists_finite_periodic_window_segments (Fact.out : 0 < p₁)
      (hr true).1 (hr true).2.2.1 hW
  letI := hI'
  letI := hJ'
  have himage (b : Bool) (z : ℝ × ℝ) :
      (h₁ ((z.1 : AddCircle p₁), (z.2 : AddCircle p₁)) : X) ∈
        (fun u => g b (Dehn.ProtectedAnnulus.endpoint true, u)) '' Metric.sphere (0 : Fin 2 → ℝ) 1 ↔
      ((z.1 : AddCircle p₁), (z.2 : AddCircle p₁)) ∈
        (fun t => (((r b t).1 : AddCircle p₁), ((r b t).2 : AddCircle p₁))) '' Icc (0 : ℝ) 1 := by
    rw [← (hr b).2.2.2]
    constructor
    · rintro ⟨t, ht, heq⟩
      exact ⟨t, ht, h₁.injective (Subtype.ext heq)⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨t, ht, congrArg (fun x => (h₁ x : X)) heq⟩
  exact exists_marked_product_of_original_periodic_windows O hI hR hconn
    hS₀ hS₁ hdis x₀ x₁ hcomponent₀ hcomponent₁
    M₀ H₀ F₀ hF₀ hFval₀ h₀ hvalue₀ M₁ hK₁ H₁ F₁ hF₁ hFval₁ h₁ hvalue₁
    g q (fun b => (hg b).1) (fun b => (hg b).2.1) (fun b => (hg b).2.2.1)
    (fun b => (hg b).2.2.2.1) (fun b => (hg b).2.2.2.2.1)
    (fun b => (hg b).2.2.2.2.2) a b c d hcd hselfA hselfB
    (fun z hz => (himage false z).trans (hwindowA z hz))
    (fun z hz => (himage true z).trans (hwindowB z hz))

end PoincareConjecture.M76.PeriodicSquare
