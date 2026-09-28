import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.NestedTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusBoundaryParameters









set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_resolving_annulus_retained_seams
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (hb : 0 < b) (hbd : b < d)
    (A : Fin 2 → Set E) (c : ∀ k, squareAnnulus L d ≃ₜ A k)
    (f : E → X) (τ : C3 → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L))
      (u : Icc (-d) d),
      f (c k ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) =
        τ (sourceTubeDiagonal k u, s)) (j : Fin 2) :
    ∃ a : P2 → X,
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      a '' squareAnnulus L d ⊆ τ '' identityTube L d ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
          τ (nestedTubeReindex j ((u, max |(u : ℝ)| b), s))) ∧
      (∀ p : squareAnnulus L d, depth L p = -d → a p = f (c j p)) ∧
      (∀ p : squareAnnulus L d, depth L p = d → a p = f (c j.rev p)) := by
  obtain ⟨hτ', himage, hfib'⟩ := nestedTubeReindex_map e (by linarith) hd j τ hτ hfib
  obtain ⟨aa, H, a, _, haemb, haPL, hH, haH, hperiod, _, hasub,
    hcorners, _, _, _⟩ :=
    exists_identity_resolving_annulus e hcompat hd hwidth hb hbd true
      (τ ∘ nestedTubeReindex j) hτ' hfib'
  refine ⟨a, haemb, haPL, hasub.trans himage.subset, ?_, ?_, ?_⟩
  · intro s hs u
    rw [← hH ((s : AddCircle (4 * L)), u), haH, hperiod s hs u]
    rfl
  · intro p hp
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hp] at hsp
    let u : Icc (-d) d := ⟨-d, by constructor <;> linarith⟩
    have hcp : (⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩ : squareAnnulus L d) = p :=
      Subtype.ext hsp.symm
    have hh := (hcorners s hs).1
    simp only [if_true, Function.comp_apply] at hh
    rw [nestedTubeReindex_corners j d s |>.1] at hh
    exact (congrArg a hsp).trans (hh.trans ((hvalue j s hs u).symm.trans
      (congrArg (fun q ↦ f (c j q)) hcp)))
  · intro p hp
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hp] at hsp
    let u : Icc (-d) d := ⟨d, by constructor <;> linarith⟩
    have hcp : (⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩ : squareAnnulus L d) = p :=
      Subtype.ext hsp.symm
    have hh := (hcorners s hs).2
    simp only [if_true, Function.comp_apply] at hh
    rw [nestedTubeReindex_corners j d s |>.2] at hh
    exact (congrArg a hsp).trans (hh.trans ((hvalue j.rev s hs u).symm.trans
      (congrArg (fun q ↦ f (c j.rev q)) hcp)))

end PoincareConjecture.M76.Dehn.Annuli
