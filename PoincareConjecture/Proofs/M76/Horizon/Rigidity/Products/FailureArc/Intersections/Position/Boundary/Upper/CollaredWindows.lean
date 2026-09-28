import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.OriginalWindows
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.TranslatedPair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.LowerRimPatches
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.RimPatchPair

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76.PeriodicSquare
open Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem exists_original_collared_pair_of_periodic_windows
    {E₀ E₁ X ι I J : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace X] [T2Space X] {e : ι → OpenPartialHomeomorph X V3}
    {R S₀ S₁ : Set X} (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (hclopen : IsClopen ((Subtype.val : frontier R → X) ⁻¹' S₁))
    {p₀ p₁ : ℝ} [Fact (0 < p₀)] [Fact (0 < p₁)]
    {K₀ : SimplicialComplex ℝ E₀} {K₁ : SimplicialComplex ℝ E₁}
    (M₀ : SourceSquareMap p₀ K₀) (H₀ : K₀.space ≃ₜ S₀)
    (F₀ : E₀ → X) (hF₀ : PolyhedralPLInCharts e F₀ K₀.space)
    (hFval₀ : ∀ x : K₀.space, F₀ x = (H₀ x : X))
    (h₀ : (AddCircle p₀ × AddCircle p₀) ≃ₜ S₀)
    (hvalue₀ : ∀ z : Square p₀, h₀ (projection p₀ z) = H₀ (M₀.map z))
    (M₁ : SourceSquareMap p₁ K₁) (hK₁ : K₁.faces.Finite) (H₁ : K₁.space ≃ₜ S₁)
    (F₁ : E₁ → X) (hF₁ : PolyhedralPLInCharts e F₁ K₁.space)
    (hFval₁ : ∀ x : K₁.space, F₁ x = (H₁ x : X))
    (h₁ : (AddCircle p₁ × AddCircle p₁) ≃ₜ S₁)
    (hvalue₁ : ∀ z : Square p₁, h₁ (projection p₁ z) = H₁ (M₁.map z))
    (f : Bool → V1 × V2 → X) (q : Bool → Q ≃ₜ AddCircle p₀)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) source)
    (hfi : ∀ i, InjOn (f i) source) (hfR : ∀ i, MapsTo (f i) source R)
    (hproper : ∀ i z, z ∈ source → (f i z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1))
    (hlower : ∀ i (z : Q), f i (endpoint false, z) =
      (h₀ (if i then (((p₀ / 2 : ℝ) : AddCircle p₀), q i z)
        else (q i z, ((p₀ / 2 : ℝ) : AddCircle p₀))) : X))
    (hupper : ∀ i (z : Q), f i (endpoint true, z) ∈ S₁)
    [Finite I] [Finite J] (a b : I → P2) (c d : J → P2)
    (hcd : ∀ j, c j ≠ d j)
    (hselfA : ∀ i k, i ≠ k →
      segment ℝ (a i) (b i) ∩ segment ℝ (a k) (b k) ⊆ {a i, b i})
    (hselfB : ∀ j k, j ≠ k →
      segment ℝ (c j) (d j) ∩ segment ℝ (c k) (d k) ⊆ {c j, d j})
    (hwindow₀ : ∀ z ∈ Icc (-p₁) (2 * p₁) ×ˢ Icc (-p₁) (2 * p₁),
      (h₁ ((z.1 : AddCircle p₁), (z.2 : AddCircle p₁)) : X) ∈
        (fun u => f false (endpoint true, u)) '' Q ↔ z ∈ ⋃ i, segment ℝ (a i) (b i))
    (hwindow₁ : ∀ z ∈ Icc (-p₁) (2 * p₁) ×ˢ Icc (-p₁) (2 * p₁),
      (h₁ ((z.1 : AddCircle p₁), (z.2 : AddCircle p₁)) : X) ∈
        (fun u => f true (endpoint true, u)) '' Q ↔ z ∈ ⋃ j, segment ℝ (c j) (d j)) :
    ∃ g : Bool → V1 × V2 → X,
      (∀ i, PolyhedralPLInCharts e (g i) source ∧ InjOn (g i) source ∧
        MapsTo (g i) source R ∧
        (∀ z ∈ source, g i z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        (∀ z : Q, g i (endpoint false, z) = f i (endpoint false, z)) ∧
        ∀ z : Q, g i (endpoint true, z) ∈ S₁) ∧
      ((g false '' source ∩ g true '' source) ∩ S₀ =
        {(h₀ (((p₀ / 2 : ℝ) : AddCircle p₀), ((p₀ / 2 : ℝ) : AddCircle p₀)) : X)}) ∧
      ∀ x ∈ g false '' source ∩ g true '' source, x ∈ frontier R →
        ∃ C : OriginalSurfacePairChart e (g false '' source) (g true '' source) x true,
          (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔
            (C.coordinates z).1.2 = 0 := by
  let k (t : AddCircle p₁ × AddCircle p₁) : X := h₁ t
  let C (i : Bool) := k ⁻¹' ((fun u => f i (endpoint true, u)) '' Q)
  have hC (i : Bool) : k '' C i = (fun u => f i (endpoint true, u)) '' Q := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ht
    · rintro _ ⟨u, hu, rfl⟩
      let x : S₁ := ⟨f i (endpoint true, u), hupper i ⟨u, hu⟩⟩
      have hx : k (h₁.symm x) = f i (endpoint true, u) :=
        congrArg Subtype.val (h₁.apply_symm_apply x)
      exact ⟨h₁.symm x, ⟨u, hu, hx.symm⟩, hx⟩
  obtain ⟨v, _, _, hpatches⟩ := M₁.exists_original_translated_window_patches H₁ F₁ hF₁
    hFval₁ h₁ hvalue₁ a b c d hcd hselfA hselfB (C false) (C true) hwindow₀ hwindow₁
  have hlowermark (i : Bool) (u : Q) : f i (endpoint false, u) ∈ S₀ := by
    rw [hlower]
    exact (h₀ _).property
  obtain ⟨j, hj, hji, hjR, _, hjlower, hjfalse, hjtrue, hjupper⟩ :=
    M₁.exists_original_pair_with_translated_upper_rim he hR hconn hS₀ hS₁ hdis hclopen
      hK₁ F₁ hF₁ H₁ hFval₁ h₁ hvalue₁ v f hf hfi hfR hproper hlowermark hupper
  let D := (fun t => t + ((v.1 : AddCircle p₁), (v.2 : AddCircle p₁))) '' C true
  have himagefalse : (fun u => j false (endpoint true, u)) '' Q = k '' C false := by
    rw [hC]
    exact image_congr (fun u hu => hjfalse ⟨u, hu⟩)
  have himagetrue : (fun u => j true (endpoint true, u)) '' Q = k '' D := by
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      let x : S₁ := ⟨f true (endpoint true, u), hupper true ⟨u, hu⟩⟩
      have hx : k (h₁.symm x) = f true (endpoint true, u) :=
        congrArg Subtype.val (h₁.apply_symm_apply x)
      refine ⟨h₁.symm x + ((v.1 : AddCircle p₁), (v.2 : AddCircle p₁)), ?_,
        (hjtrue ⟨u, hu⟩).symm⟩
      exact ⟨h₁.symm x, ⟨u, hu, hx.symm⟩, rfl⟩
    · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      obtain ⟨u, hu, hut⟩ := ht
      have ht' : h₁.symm ⟨f true (endpoint true, u), hupper true ⟨u, hu⟩⟩ = t := by
        apply h₁.injective
        rw [h₁.apply_symm_apply]
        exact Subtype.ext hut
      refine ⟨u, hu, ?_⟩
      change j true (endpoint true, u) = k (t + ((v.1 : AddCircle p₁), (v.2 : AddCircle p₁)))
      rw [hjtrue ⟨u, hu⟩, ht']
  let S (b : Bool) := if b then S₁ else S₀
  have hjmark (i b : Bool) : MapsTo (fun u => j i (endpoint b, u)) Q (S b) := by
    intro u hu
    cases b
    · change j i (endpoint false, u) ∈ S₀
      rw [hjlower i ⟨u, hu⟩]
      exact hlowermark i ⟨u, hu⟩
    · exact hjupper i ⟨u, hu⟩
  have hjpatch : ∀ b x,
      x ∈ (fun u => j false (endpoint b, u)) '' Q ∩
        (fun u => j true (endpoint b, u)) '' Q →
      ∃ d : ℝ, 0 < d ∧ ∃ u : P2 → X,
        PolyhedralPLInCharts e u (Icc (-d) d ×ˢ Icc (-d) d) ∧
        InjOn u (Icc (-d) d ×ˢ Icc (-d) d) ∧
        MapsTo u (Icc (-d) d ×ˢ Icc (-d) d) (S b) ∧ u 0 = x ∧
        (∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d,
          u z ∈ (fun w => j false (endpoint b, w)) '' Q ↔ z.2 = 0) ∧
        ∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d,
          u z ∈ (fun w => j true (endpoint b, w)) '' Q ↔ z.1 = 0 := by
    intro b x hx
    cases b
    · exact M₀.exists_original_coordinate_rim_patches H₀ F₀ hF₀ hFval₀ h₀ hvalue₀
        (fun i u => j i (endpoint false, u)) q
        (fun i u => (hjlower i u).trans (hlower i u)) x hx
    · rw [himagefalse, himagetrue] at hx
      obtain ⟨δ, hδ, u, hu, hui, huS, hu0, huaxis₀, huaxis₁⟩ := hpatches x hx
      exact ⟨δ, hδ, u, hu, hui, huS, hu0,
        (fun z hz => by rw [himagefalse]; exact huaxis₀ z hz),
        (fun z hz => by rw [himagetrue]; exact huaxis₁ z hz)⟩
  obtain ⟨g, hg, hgboundary⟩ := he.exists_original_collared_pair_of_rim_patches hR hconn S
    (fun b => by cases b; exact hS₀; exact hS₁) hdis j hj hji hjR hjmark hjpatch
  have hglower (i : Bool) (u : Q) : g i (endpoint false, u) = f i (endpoint false, u) :=
    ((hg i).2.2.2.2 false u u.property).trans (hjlower i u)
  have hgupper (i : Bool) (u : Q) : g i (endpoint true, u) ∈ S₁ := by
    rw [(hg i).2.2.2.2 true u u.property]
    exact hjupper i u
  refine ⟨g, (fun i => ⟨(hg i).1, (hg i).2.1, (hg i).2.2.1,
    (hg i).2.2.2.1, hglower i, hgupper i⟩), ?_, hgboundary⟩
  exact coordinate_proper_annuli_intersection_on_mark hS₀ hdis h₀ q
    ((p₀ / 2 : ℝ) : AddCircle p₀) g
    (fun i z => (hg i).2.2.2.1 z z.property)
    (fun u => (hglower false u).trans (hlower false u))
    (fun u => (hglower true u).trans (hlower true u)) hgupper

end PoincareConjecture.M76.PeriodicSquare
