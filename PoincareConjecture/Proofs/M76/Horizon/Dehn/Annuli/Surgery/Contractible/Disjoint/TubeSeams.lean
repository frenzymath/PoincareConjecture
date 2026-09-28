import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.TubeAnnulus








set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_disjoint_resolving_annuli_retained_seams
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (A : Fin 2 → Set P2) (c : ∀ k, squareAnnulus L d ≃ₜ A k)
    (f : P2 → X) (τ : C3 → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f (c k ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s)) :
    ∃ a : Fin 2 → P2 → X,
      (∀ k, Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a k p)) ∧
      (∀ k, PolyhedralPLInCharts e (a k) (squareAnnulus L d)) ∧
      (∀ k, a k '' squareAnnulus L d ⊆ τ '' identityTube L d) ∧
      Disjoint (a 0 '' squareAnnulus L d) (a 1 '' squareAnnulus L d) ∧
      (∀ k (p : squareAnnulus L d), depth L p = -d → a k p = f (c k p)) ∧
      (∀ k (p : squareAnnulus L d), depth L p = d → a k p = f (c k.rev p)) := by
  classical
  choose a hemb hPL himage hperiod hout hin using
    exists_resolving_annulus_retained_seams e hcompat hd hwidth hb hbd A c f τ hτ hfib hvalue
  refine ⟨a, hemb, hPL, himage, ?_, hout, hin⟩
  apply disjoint_left.mpr
  rintro z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩
  obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth ⟨p, hp⟩
  obtain ⟨t, ht, htq⟩ := exists_period_parameter_of_depth hd hwidth ⟨q, hq⟩
  let u : Icc (-d) d := ⟨depth L p, mem_squareAnnulus_iff_depth.mp hp⟩
  let v : Icc (-d) d := ⟨depth L q, mem_squareAnnulus_iff_depth.mp hq⟩
  have hpval := hperiod 0 s hs u
  have hqval := hperiod 1 t ht v
  rw [← hsp] at hpval
  rw [← htq] at hqval
  have hm (w : Icc (-d) d) (r : ℝ) (hr : r ∈ Icc 0 (4 * L)) (k : Fin 2) :
      nestedTubeReindex k (((w : ℝ), max |(w : ℝ)| b), r) ∈ identityTube L d := by
    apply (nestedTubeReindex_mem k L d _).mpr
    have habs : |(w : ℝ)| ≤ d := abs_le.mpr w.property
    have hmax : max |(w : ℝ)| b ≤ d := max_le habs hbd.le
    have hmin : -d ≤ max |(w : ℝ)| b := by linarith [le_max_right |(w : ℝ)| b]
    exact ⟨⟨w.property, hmin, hmax⟩, hr⟩
  have he := ((hfib _ (hm u s hs 0) _ (hm v t ht 1)).mp
    (hpval.symm.trans (hpz.trans (hqz.symm.trans hqval)))).1
  have he' := congrArg Prod.snd he
  change -max |(u : ℝ)| b = max |(v : ℝ)| b at he'
  linarith [le_max_right |(u : ℝ)| b, le_max_right |(v : ℝ)| b]

end PoincareConjecture.M76.Dehn.Annuli
