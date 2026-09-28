import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedOrdinary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Ordinary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.SourceAlternatives
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.TubeExchange









set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_contractible_paired_ordinary_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d b : ℝ} (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : ∀ k, closure (B k).outer.inside ⊆ interior J.space)
    (hdis : Disjoint (A 0) (A 1))
    (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J.space)
    (R : Set X) (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (hcollision : Disjoint (doubleLocusOn f J.space) (frontier J.space))
    (hcross : ∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f J.space R x y))
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hτR : τ '' identityTube L d ⊆ interior R)
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f ((B k).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' identityTube L d) = A 0 ∪ A 1)
    (M : SourceCircleDecomposition f J.space) (i k : M.Index)
    (hmiddle₀ : (fun p : squareAnnulus L d ↦ ((B 0).chart p : P2)) ''
      {p | depth L p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus L d ↦ ((B 1).chart p : P2)) ''
      {p | depth L p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A 0, x ∈ doubleLocusOn f J.space → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A 1, x ∈ doubleLocusOn f J.space → x ∈ M.pieces k) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g J.space ∧ MapsTo g J.space R ∧
      EqOn g f (frontier J.space) ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      Disjoint (doubleLocusOn g J.space) (frontier J.space) ∧
      IsCompact (doubleLocusOn g J.space) ∧
      (∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g J.space R x y)) ∧
      IsLocallyInjective (fun x : J.space ↦ g x) ∧
      Nonempty (SourceCircleDecomposition g J.space) ∧
      Nat.card (ConnectedComponents (doubleLocusOn g J.space)) <
        Nat.card (ConnectedComponents (doubleLocusOn f J.space)) := by
  rcases disjoint_oriented_collars_source_cases (B 0) (B 1) hdis with hn | hn | hp
  · exact exists_nested_contractible_ordinary_map e hcompat J hJ B (hcontract 0) hn
      hd hwidth hb hbd f hf R hin hfront hcollision hcross τ hτ hτR hfib hvalue hpreimage
      M i k hmiddle₀ hmiddle₁ htrace₀ htrace₁
  · obtain ⟨hτ', himage, hfib'⟩ := pairedTubeExchange_map e (by linarith) hd τ hτ hfib
    let B' : ∀ l : Fin 2, OrientedPolygonCollar L d (A l.rev) := fun l ↦ B l.rev
    have hvalue' (l : Fin 2) (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
        f ((B' l).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          annulus_period_point_mem hd hwidth _ u⟩) =
            (τ ∘ pairedTubeExchange) (sourceTubeDiagonal l u, s) := by
      rw [Function.comp_apply, pairedTubeExchange_diagonal]
      exact hvalue l.rev s hs u
    have hpre' : J.space ∩ f ⁻¹' ((τ ∘ pairedTubeExchange) '' identityTube L d) =
        A (0 : Fin 2).rev ∪ A (1 : Fin 2).rev := by
      rw [himage, hpreimage]
      exact union_comm _ _
    exact exists_nested_contractible_ordinary_map e hcompat J hJ B' (hcontract 1) hn
      hd hwidth hb hbd f hf R hin hfront hcollision hcross (τ ∘ pairedTubeExchange)
      hτ' (himage.subset.trans hτR) hfib' hvalue' hpre'
      M k i hmiddle₁ hmiddle₀ htrace₁ htrace₀
  · exact exists_disjoint_contractible_ordinary_map e hcompat J hJ B hcontract hp
      hd hwidth hb hbd f hf R hin hfront hcollision hcross τ hτ hτR hfib hvalue hpreimage
      M i k hmiddle₀ hmiddle₁ htrace₀ htrace₁

end PoincareConjecture.M76.Dehn.Annuli
