import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ReflectionBoundaryValues
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

theorem exists_boundary_matched_reflection_annulus
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : ((ℝ × ℝ) × ℝ) → X)
    (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0)))) :
    ∃ g : (ℝ × ℝ) → X,
      PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ g p) ∧
      g '' squareAnnulus L d ⊆ τ '' singleReflectionTube L d ∧
      (∀ s ∈ Icc 0 (4 * L),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) =
          (if s ≤ 2 * L then τ ((-d, -d), s) else τ ((-d, d), s - 2 * L)) ∧
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), d)) =
          (if s ≤ 2 * L then τ ((d, d), s) else τ ((d, -d), s - 2 * L))) ∧
      squareAnnulus L d ∩ g ⁻¹' (τ '' singleReflectionTubeSide L d) =
        frontier (squareAnnulus L d) := by
  have hL : 0 < L := by linarith
  obtain ⟨a, E, g, _, hgemb, hgPL, _, _, _, _, hgimage, hcurves, hfront⟩ :=
    exists_single_period_reflection_resolving_annulus e hcompat hd hwidth hb hbd τ hτ hfib
  obtain ⟨c, hc, _, hcdepth, hcperiod⟩ := exists_square_annulus_half_period_shear hd hwidth
  obtain ⟨q, hq, hqval⟩ := hc
  have hqmap : MapsTo q (squareAnnulus L d) (squareAnnulus L d) := by
    intro x hx
    rw [← hqval ⟨x, hx⟩]
    exact (c ⟨x, hx⟩).property
  have hqimage : q '' squareAnnulus L d = squareAnnulus L d := by
    apply Subset.antisymm hqmap.image_subset
    intro x hx
    refine ⟨c.symm ⟨x, hx⟩, (c.symm ⟨x, hx⟩).property, ?_⟩
    rw [← hqval, c.apply_symm_apply]
  have hqdepth {x : ℝ × ℝ} (hx : x ∈ squareAnnulus L d) :
      depth L (q x) = depth L x := by
    rw [← hqval ⟨x, hx⟩]
    exact hcdepth ⟨x, hx⟩
  obtain ⟨K, hK, hKs⟩ := exists_finite_square_annulus_complex hd hwidth
  have hPL : PolyhedralPLInCharts e (g ∘ q) (squareAnnulus L d) := by
    rw [← hKs]
    exact hgPL.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hq) (hKs.symm ▸ hqmap)
  have hemb : Topology.IsEmbedding (fun p : squareAnnulus L d ↦ g (q p)) := by
    have heq : (fun p : squareAnnulus L d ↦ g (q p)) =
        (fun p : squareAnnulus L d ↦ g p) ∘ c := by
      funext p
      rw [Function.comp_apply, hqval]
    rw [heq]
    exact hgemb.comp c.isEmbedding
  have hend : τ ((-d, d), 2 * L) = τ ((-d, -d), 0) := by
    apply (hfib _ (by constructor <;> dsimp [singleReflectionTube] <;> constructor <;>
      first | constructor <;> linarith | linarith)
      _ (by constructor <;> dsimp [singleReflectionTube] <;> constructor <;>
      first | constructor <;> linarith | linarith)).mpr
    exact Or.inr ⟨by simp, Or.inr ⟨rfl, rfl⟩⟩
  have hnegative := reflection_annulus_shifted_negative_boundary hd hwidth τ g hend
    (fun s hs ↦ (hcurves s hs).1)
  have hqperiod (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      q (annulusMap L hL ((s : AddCircle (4 * L)), u)) =
        annulusMap L hL (((s + (L - (L / d) * u) : ℝ) : AddCircle (4 * L)), u) := by
    rw [← hqval ⟨_, annulus_period_point_mem hd hwidth _ u⟩]
    exact hcperiod s hs u
  refine ⟨g ∘ q, hPL, hemb, ?_, ?_, ?_⟩
  · rw [image_comp, hqimage]
    exact hgimage
  · intro s hs
    constructor
    · change g (q _) = _
      rw [hqperiod s hs ⟨-d, ⟨le_rfl, by linarith⟩⟩]
      simpa only [mul_neg, div_mul_cancel₀ _ hd.ne', sub_neg_eq_add,
        ← two_mul] using hnegative s hs
    · change g (q _) = _
      rw [hqperiod s hs ⟨d, ⟨by linarith, le_rfl⟩⟩]
      simpa only [div_mul_cancel₀ _ hd.ne', sub_self, add_zero] using (hcurves s hs).2
  · ext x
    constructor
    · rintro ⟨hx, hxside⟩
      have hxfront : q x ∈ frontier (squareAnnulus L d) :=
        hfront.subset ⟨hqmap hx, hxside⟩
      apply (mem_frontier_squareAnnulus_iff hd (by linarith) hx).mpr
      rw [← hqdepth hx]
      exact (mem_frontier_squareAnnulus_iff hd (by linarith) (hqmap hx)).mp hxfront
    · intro hxfront
      have hx : x ∈ squareAnnulus L d :=
        (isClosed_Icc.prod isClosed_Icc).sdiff (isOpen_Ioo.prod isOpen_Ioo)
          |>.frontier_subset hxfront
      refine ⟨hx, hfront.symm.subset ?_ |>.2⟩
      apply (mem_frontier_squareAnnulus_iff hd (by linarith) (hqmap hx)).mpr
      rw [hqdepth hx]
      exact (mem_frontier_squareAnnulus_iff hd (by linarith) hx).mp hxfront

end Dehn
