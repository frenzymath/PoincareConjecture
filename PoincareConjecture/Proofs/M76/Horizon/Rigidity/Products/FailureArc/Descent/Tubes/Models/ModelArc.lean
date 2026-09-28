import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Models.MarkedModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Models.Parameters









set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V3" => (Fin 3 → ℝ)
local notation "I01" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {sourceSet rimSet : Set E} [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
  {old : SourceDoubleComponents e f sourceSet rimSet R} {i : old.Index}

omit [T2Space X] in
theorem SourceIntervalMarkedModel.graph_inverse (D : SourceIntervalMarkedModel old i)
    (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) : D.graph (D.inverse z) = z := by
  rw [D.inverse_value ⟨z, hz⟩, ← D.homeomorph_value, D.homeomorph.apply_symm_apply]

omit [T2Space X] in

theorem SourceIntervalMarkedModel.mem_mark_image (D : SourceIntervalMarkedModel old i)
    {Z : Set X} {L : Set (D.sample → ℝ × V3)}
    (hL : L = D.graph '' (D.core ∩ Z))
    (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) :
    z ∈ L ↔ (D.inverse z : X) ∈ Z := by
  rw [hL]
  constructor
  · rintro ⟨x, hx, hval⟩
    have heq := D.graph_separates x hx.1 (D.inverse z)
      (hval.trans (D.graph_inverse z hz).symm)
    exact heq ▸ hx.2
  · intro hx
    exact ⟨D.inverse z, ⟨(D.inverse z).property, hx⟩, D.graph_inverse z hz⟩

omit [T2Space X] in

theorem SourceIntervalMarkedModel.selected_clip (D : SourceIntervalMarkedModel old i) :
    (D.clips 2).space = old.pieces i := by
  rw [(D.clips_data 2).2.1, D.selected_source]
  exact inter_eq_left.mpr (fun x hx ↦ show f x ∈ D.core from
    interior_subset (D.core_neighborhood ⟨x, hx, rfl⟩))

omit [T2Space X] in


theorem SourceIntervalMarkedModel.exists_arc_parameters
    (D : SourceIntervalMarkedModel old i)
    (hball : IsFinitePLBallPair ℝ (old.pieces i) (old.pieces i ∩ rimSet)) :
    ∃ (a : I01 ≃ₜ old.pieces i) (b : I01 ≃ₜ (D.marks (.inr 2)).space),
      a.IsFinitePL ∧ b.IsFinitePL ∧
      (∀ u : I01, (b u : D.sample → ℝ × V3) = D.graph (f (a u))) ∧
      (∀ u : I01, (D.inverse (b u) : X) = f (a u)) ∧
      (D.marks (.inr 2)).space ∩ (D.marks (.inl true)).space =
        {(b 0 : D.sample → ℝ × V3), (b 1 : D.sample → ℝ × V3)} := by
  obtain ⟨_, a, _, arc, ha, _, _, _, _, _, _, hvals, _, hends, _⟩ :=
    old.interval i hball
  have hSC : MapsTo f (old.pieces i) D.core :=
    fun x hx ↦ interior_subset (D.core_neighborhood ⟨x, hx, rfl⟩)
  have hPL : FinitePiecewiseAffineOn (D.graph ∘ f) (old.pieces i) := by
    simpa only [D.selected_clip] using (D.clips_data 2).2.2.1
  have hA : (D.marks (.inr 2)).space = (D.graph ∘ f) '' old.pieces i :=
    (D.clips_data 2).2.2.2.symm.trans
      (congrArg (fun S : Set E ↦ (D.graph ∘ f) '' S) D.selected_clip)
  have hB (z : D.sample → ℝ × V3) (hz : z ∈ (D.marks (.inr 2)).space) :
      z ∈ (D.marks (.inl true)).space ↔ (D.inverse z : X) ∈ frontier R :=
    D.mem_mark_image D.frontier_image z
      (SimplicialComplex.space_subset_of_le (D.marks_full (.inr 2)).1 hz)
  have hboundary (u : I01) : f (a u) ∈ frontier R ↔ u = 0 ∨ u = 1 := by
    rw [← (hvals u).1]
    exact hends u
  obtain ⟨b, hb, hbval, hgb, hcontact⟩ := exists_model_interval_parameters D.core D.complex
    D.homeomorph D.graph D.inverse D.homeomorph_value D.inverse_value a ha hSC hPL
      (old.injOn_piece_of_mate_ne i D.mate_ne) (D.marks (.inr 2)) (D.marks (.inl true))
        hA hB hboundary
  exact ⟨a, b, ha, hb, hbval, hgb, hcontact⟩

end PoincareConjecture.M76.Dehn.Annuli
