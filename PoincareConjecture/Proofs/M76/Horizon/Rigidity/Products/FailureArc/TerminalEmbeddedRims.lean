import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalPolygons
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquarePolygonUniformBoundary











set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.MarkedTerminalRegion

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1



theorem exists_disjoint_essential_embedded_rims
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3}
    {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → M}
    {r : M → ℝ} {C R : Set M} {st : Stage e S g r C}
    (N : MarkedTerminalRegion st R) (hS : S.space = ProtectedAnnulus.source)
    (hfront : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (f : C(ProtectedAnnulus.source, R))
    (hgf : ∀ x : ProtectedAnnulus.source, g x = (f x : M))
    (hessential : ∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic)
    (F : Bool → Set M) (hF : Disjoint (F false) (F true))
    (hmark : ∀ (b : Bool) (u : Q2), g (ProtectedAnnulus.endpoint b, u) ∈ F b) :
    ∃ (a : Bool → V2 → (N.sample → ℝ × V3)) (gamma : Bool → C(Q2, N.boundary.space)),
      (∀ b, FinitePiecewiseAffineOn (a b) Q2) ∧
      (∀ b, InjOn (a b) Q2) ∧
      (∀ (b : Bool) (u : Q2), (gamma b u : N.sample → ℝ × V3) = a b u) ∧
      (∀ b, ¬ (N.originalProjection.comp (gamma b)).Nullhomotopic) ∧
      (∀ b, a b '' Q2 ⊆ range (fun u =>
        (N.singularBoundaryRim hS hfront b u : N.sample → ℝ × V3))) ∧
      Disjoint (a false '' Q2) (a true '' Q2) := by
  classical
  have hex (b : Bool) :
      ∃ (a : V2 → (N.sample → ℝ × V3)) (gamma : C(Q2, N.boundary.space)),
        FinitePiecewiseAffineOn a Q2 ∧ InjOn a Q2 ∧
        (∀ u : Q2, (gamma u : N.sample → ℝ × V3) = a u) ∧
        ¬ (N.originalProjection.comp gamma).Nullhomotopic ∧
        a '' Q2 ⊆ range (fun u =>
          (N.singularBoundaryRim hS hfront b u : N.sample → ℝ × V3)) := by
    obtain ⟨n, P, hPB, hinj, hP, hPrange, hnon⟩ :=
      N.exists_essential_rim_polygon hS hfront f hgf hessential b
    obtain ⟨H, hH, _, _⟩ := exists_square_polygon_uniform_boundary P hP hinj
    obtain ⟨a, ha, hHa⟩ := hH
    let inc : C(P.boundary ℝ, N.boundary.space) := ContinuousMap.inclusion hPB
    let gamma : C(Q2, N.boundary.space) := inc.comp ⟨H, H.continuous⟩
    have hai : InjOn a Q2 := by
      intro x hx y hy hxy
      have hval : H ⟨x, hx⟩ = H ⟨y, hy⟩ := by
        apply Subtype.ext
        rw [hHa, hHa]
        exact hxy
      exact congrArg Subtype.val (H.injective hval)
    have hg : ¬ (N.originalProjection.comp gamma).Nullhomotopic := by
      intro hn
      have heq : (N.originalProjection.comp gamma).comp ⟨H.symm, H.symm.continuous⟩ =
          N.originalProjection.comp inc := by
        ext x
        change (N.originalProjection (inc (H (H.symm x))) : M) =
          (N.originalProjection (inc x) : M)
        rw [H.apply_symm_apply]
      exact hnon (heq ▸ hn.comp_left ⟨H.symm, H.symm.continuous⟩)
    refine ⟨a, gamma, ha, hai, hHa, hg, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [← hHa ⟨u, hu⟩]
    exact hPrange (H ⟨u, hu⟩).property
  choose a gamma ha hai hgamma hnon hsub using hex
  refine ⟨a, gamma, ha, hai, hgamma, hnon, hsub, ?_⟩
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨u, hu⟩ := hsub false hx
  obtain ⟨v, hv⟩ := hsub true hy
  have heq : N.singularBoundaryRim hS hfront true v =
      N.singularBoundaryRim hS hfront false u := Subtype.ext (hv.trans hu.symm)
  exact disjoint_left.mp (N.singularBoundaryRim_ranges_disjoint hS hfront F hF hmark)
    ⟨u, rfl⟩ ⟨v, heq⟩

end Geometry.OriginalPLTower.MarkedTerminalRegion
