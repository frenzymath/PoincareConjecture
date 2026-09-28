import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.PolyhedralSource
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.OpenMarks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialAnnulus

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem boundaryLoopIterate_range_subset {X : Type*} [TopologicalSpace X] {x : X}
    (alpha : Path x x) (n : ℕ) : range (boundaryLoopIterate alpha n) ⊆ range alpha := by
  induction n with
  | zero =>
    rw [boundaryLoopIterate, Path.refl_range]
    exact singleton_subset_iff.mpr ⟨0, alpha.source⟩
  | succ n hn =>
    rw [boundaryLoopIterate, Path.trans_range]
    exact union_subset Subset.rfl hn

theorem exists_marked_PL_annulus_of_commensurable_open_marks
    {E₀ E₁ X ι : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (hi₁ : ∀ x, (i₁ x : X) ∈ F true)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (alpha : Path e₀ e₀) (halpha : ∀ t, (i₀ (alpha t) : X) ∈ F false) :
    ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path e₁ e₁) (g : (V1 × V2) → X)
      (gamma gamma₀ : ∀ b, C(Q2, F b)),
      PolyhedralPLInCharts e g source ∧ MapsTo g source R ∧
      (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
      (∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b))) ∧
      (∀ s : unitInterval, (gamma false (squareRimLoop s) : X) =
        (i₀ (boundaryLoopIterate alpha n s) : X)) ∧
      (∀ s : unitInterval, (gamma true (squareRimLoop s) : X) = (i₁ (beta s) : X)) := by
  obtain ⟨n, hn, beta, f, hf₀, hf₁⟩ :=
    exists_polyhedral_source_singular_annulus i₀ i₁ e₀ e₁ k hc alpha
  let inc (b : Bool) : C(Q2, source) :=
    ⟨fun u => ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
  have hinc₀ (u : Q2) : inc false u = cylinder (0, u) := (cylinder_zero u).symm
  have hinc₁ (u : Q2) : inc true u = cylinder (1, u) := (cylinder_one u).symm
  have hfF (b : Bool) (u : Q2) : (f (inc b u) : X) ∈ F b := by
    obtain ⟨s, rfl⟩ := surjective_squareRimLoop u
    cases b
    · rw [hinc₀, hf₀]
      obtain ⟨t, ht⟩ := boundaryLoopIterate_range_subset alpha n (mem_range_self s)
      rw [← ht]
      exact halpha t
    · rw [hinc₁, hf₁]
      exact hi₁ _
  let gamma (b : Bool) : C(Q2, F b) :=
    ⟨fun u => ⟨f (inc b u), hfF b u⟩,
      (continuous_subtype_val.comp (f.continuous.comp (inc b).continuous)).subtype_mk _⟩
  obtain ⟨g, a, hg, hga, gamma₀, hrim, hhom⟩ :=
    exists_marked_PL_annulus_pair_of_disjoint_open he F hF hFopen hdis f gamma (fun _ _ => rfl)
  refine ⟨n, hn, beta, g, gamma, gamma₀, hg, ?_, hrim, hhom, ?_, ?_⟩
  · intro x hx
    rw [hga ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property
  · intro s
    change (f (inc false (squareRimLoop s)) : X) = _
    rw [hinc₀, hf₀]
  · intro s
    change (f (inc true (squareRimLoop s)) : X) = _
    rw [hinc₁, hf₁]

theorem exists_essential_marked_PL_annulus_of_commensurable_open_marks
    {E₀ E₁ X ι : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (hi₁ : ∀ x, (i₁ x : X) ∈ F true)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (hinj : Function.Injective (FundamentalGroup.map i₀ e₀))
    (alpha : Path e₀ e₀) (halpha : ∀ t, (i₀ (alpha t) : X) ∈ F false)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0) :
    ∃ (g : (V1 × V2) → X) (f : C(source, R)),
      PolyhedralPLInCharts e g source ∧
      (∀ x : source, g x = (f x : X)) ∧
      (∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ F b) ∧
      (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
      ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path e₁ e₁) (gamma gamma₀ : ∀ b, C(Q2, F b)),
        (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
        (∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b))) ∧
        (∀ s : unitInterval, (gamma false (squareRimLoop s) : X) =
          (i₀ (boundaryLoopIterate alpha n s) : X)) ∧
        (∀ s : unitInterval, (gamma true (squareRimLoop s) : X) = (i₁ (beta s) : X)) := by
  obtain ⟨n, hn, beta, g, gamma, gamma₀, hg, hgR, hrim, hhom, hleft, hright⟩ :=
    exists_marked_PL_annulus_of_commensurable_open_marks he F hF hFopen hdis
      i₀ i₁ hi₁ e₀ e₁ k hc alpha halpha
  let f : C(source, R) :=
    ⟨fun x => ⟨g x, hgR x.property⟩, hg.continuousOn.domRestrict.subtype_mk _⟩
  let inc (b : Bool) : C(F b, R) :=
    ContinuousMap.inclusion ((hF b).trans he.closed.frontier_subset)
  have hnegative : ¬ (sourceAnnulusRim f false).Nullhomotopic := by
    have heq : (inc false).comp (gamma₀ false) = sourceAnnulusRim f false := by
      ext u
      exact (hrim false u).symm
    rw [← heq]
    apply not_nullhomotopic_of_boundary_power_homotopy i₀ e₀ hinj alpha ha n hn
      ((inc false).comp (gamma false)) ((inc false).comp (gamma₀ false))
      (fun s => Subtype.ext (hleft s))
    exact (ContinuousMap.Homotopic.refl (inc false)).comp (hhom false)
  have hessential (b : Bool) : ¬ (sourceAnnulusRim f b).Nullhomotopic := by
    cases b
    · exact hnegative
    · rintro ⟨y, hy⟩
      exact hnegative ⟨y, ContinuousMap.Homotopic.trans ⟨sourceAnnulusRimHomotopy f⟩ hy⟩
  refine ⟨g, f, hg, fun _ => rfl, ?_, hessential,
    n, hn, beta, gamma, gamma₀, hrim, hhom, hleft, hright⟩
  intro b u
  rw [hrim]
  exact (gamma₀ b u).property

end PoincareConjecture.M76
