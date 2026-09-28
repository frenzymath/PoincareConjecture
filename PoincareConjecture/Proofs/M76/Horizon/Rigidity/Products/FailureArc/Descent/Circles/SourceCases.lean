import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Circles.MixedCollars



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem paired_collar_source_cases_of_essential
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    {R : Set X} (period : Circle ≃ₜ Q) {l d : ℝ} (hd : 0 < d) (hwidth : 4 * d < l)
    (A : Fin 2 → Set P2) (B : ∀ k, OrientedPolygonCollar l d (A k))
    (hA : ∀ k, A k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (hdis : Disjoint (A 0) (A 1))
    (f₀ : P2 → X) (hf₀ : PolyhedralPLInCharts e f₀ Ann)
    (hfR : MapsTo f₀ Ann R)
    (rim : C(Q, R)) (hessential : ¬ rim.Nullhomotopic)
    (hrim : ∀ u : Q, f₀ (annulusRimPoint false (period.symm u)) = (rim u : X))
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (identityTube l d))
    (hτR : MapsTo τ (identityTube l d) R)
    (hfib : ∀ z ∈ identityTube l d, ∀ w ∈ identityTube l d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * l)) = (w.2 : AddCircle (4 * l)))
    (hvalue : ∀ (k : Fin 2) (t : ℝ) (_ht : t ∈ Icc 0 (4 * l)) (u : Icc (-d) d),
      f₀ ((B k).chart ⟨annulusMap l (by linarith) ((t : AddCircle (4 * l)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, t)) :
    (∀ k, closure (B k).outer.inside ⊆
      {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1}) ∨
      ∃ j : Fin 2, annulusSquare 8 1 ⊆ (B j.rev).outer.inside ∧
        closure (B j.rev).outer.inside ⊆ (B j).inner.inside := by
  have hmixed (j : Fin 2)
      (he : annulusSquare 8 1 ⊆ (B j).outer.inside)
      (hc : closure (B j.rev).outer.inside ⊆
        {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1}) : False :=
    hessential (mixed_collar_rim_nullhomotopic_in_region e hcompat period hd hwidth
      A B j hA he hc f₀ hf₀ hfR rim hrim τ hτ hτR hfib hvalue)
  rcases (Annuli.oriented_collar_disk_or_enclosing (B 0) (hA 0)).2.2.2 with he₀ | hc₀
  · have he₀' : annulusSquare 8 1 ⊆ (B 0).outer.inside :=
      fun x hx ↦ (B 0).nested (subset_closure (he₀ hx))
    rcases (Annuli.oriented_collar_disk_or_enclosing (B 1) (hA 1)).2.2.2 with he₁ | hc₁
    · have he₁' : annulusSquare 8 1 ⊆ (B 1).outer.inside :=
        fun x hx ↦ (B 1).nested (subset_closure (he₁ hx))
      rcases Annuli.disjoint_oriented_collars_source_cases (B 0) (B 1) hdis with hn | hn | hh
      · exact Or.inr ⟨0, he₁', hn⟩
      · exact Or.inr ⟨1, he₀', hn⟩
      · have hx : (4, 4) ∈ annulusSquare 8 1 := by norm_num [annulusSquare]
        exact (disjoint_left.mp hh (subset_closure (he₀' hx))
          (subset_closure (he₁' hx))).elim
    · exact (hmixed 0 he₀' hc₁).elim
  · rcases (Annuli.oriented_collar_disk_or_enclosing (B 1) (hA 1)).2.2.2 with he₁ | hc₁
    · have he₁' : annulusSquare 8 1 ⊆ (B 1).outer.inside :=
        fun x hx ↦ (B 1).nested (subset_closure (he₁ hx))
      exact (hmixed 1 he₁' hc₀).elim
    · refine Or.inl ?_
      intro k
      fin_cases k
      · exact hc₀
      · exact hc₁

end PoincareConjecture.M76.Dehn.Annuli
