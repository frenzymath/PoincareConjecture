import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Circles.Step



set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1



theorem exists_embedded_planar_region_annulus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (period : Circle ≃ₜ Q) {R : Set X} (he : PLDomain e R)
    (f₀ : P2 → X) (hf : PolyhedralPLInCharts e f₀ Ann)
    (hin : MapsTo f₀ Ann R)
    (hproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (rim : C(Q, R)) (hessential : ¬ rim.Nullhomotopic)
    (hrim : ∀ u : Q, f₀ (annulusRimPoint false (period.symm u)) = (rim u : X))
    (M : SourceCircleDecomposition f₀ Ann)
    (hinterior : MapsTo f₀ (doubleLocusOn f₀ Ann) (interior R))
    (hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → f₀ x = f₀ y →
      Nonempty (RawSourceCrossing e f₀ Ann R x y)) :
    ∃ (g : P2 → X) (q : Bool → Circle ≃ₜ Circle),
      PolyhedralPLInCharts e g Ann ∧ IsEmbedding (fun x : Ann ↦ g x) ∧
      MapsTo g Ann R ∧
      (∀ x ∈ Ann, g x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      ∀ b z, g (annulusRimPoint b z) = f₀ (annulusRimPoint b (q b z)) := by
  classical
  generalize hn : Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann)) = n
  induction n using Nat.strong_induction_on generalizing f₀ rim with
  | h n ih =>
    by_cases hz : Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann)) = 0
    · exact ⟨f₀, fun _ ↦ Homeomorph.refl _, hf,
        M.isEmbedding_of_component_count_zero isCompact_planar_annulus hf.continuousOn hz,
        hin, hproper, fun _ _ ↦ rfl⟩
    obtain ⟨g, q, hg, hgin, hgproper, hgwhole, hginterior, hgraw, ⟨N⟩, hdec⟩ :=
      exists_decreasing_planar_region_annulus e hcompat period he f₀ hf hin
        hproper rim hessential hrim M hinterior hcross (Nat.pos_of_ne_zero hz)
    let p : Q ≃ₜ Q := (period.symm.trans (q false)).trans period
    let rim' : C(Q, R) := rim.comp (p : C(Q, Q))
    have hrim' (u : Q) : g (annulusRimPoint false (period.symm u)) = (rim' u : X) := by
      rw [hgwhole]
      change f₀ (annulusRimPoint false (q false (period.symm u))) = (rim (p u) : X)
      have hh := hrim (p u)
      simpa only [p, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] using hh
    have hessential' : ¬ rim'.Nullhomotopic := by
      intro hh
      have heq : rim'.comp (p.symm : C(Q, Q)) = rim := by
        ext u
        exact congrArg (fun v ↦ (rim v : X)) (p.apply_symm_apply u)
      exact hessential (heq ▸ hh.comp_left (p.symm : C(Q, Q)))
    rw [hn] at hdec
    obtain ⟨G, q', hG, hGi, hGin, hGproper, hGwhole⟩ :=
      ih _ hdec g hg hgin hgproper rim' hessential' hrim' N hginterior hgraw rfl
    refine ⟨G, fun b ↦ (q' b).trans (q b), hG, hGi, hGin, hGproper, ?_⟩
    intro b z
    exact (hGwhole b z).trans (hgwhole b (q' b z))

end PoincareConjecture.M76.Dehn.Annuli
