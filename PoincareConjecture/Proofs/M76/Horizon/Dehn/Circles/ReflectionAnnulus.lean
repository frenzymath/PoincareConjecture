import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusPeriodMap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalCrossingResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

def reflectionTube (L d : ℝ) : Set C3 :=
  (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc 0 (4 * L)

def reflectionTubeSide (L d : ℝ) : Set C3 :=
  {z | z ∈ reflectionTube L d ∧ (|z.1.1| = d ∨ |z.1.2| = d)}

private theorem finitePL_upper_strip {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (b : ℝ) :
    FinitePiecewiseAffineOn (strip b true) (rectangle (4 * L) d) := by
  have hrect := (isFinitePLBallPair_Icc (show (0 : ℝ) < 4 * L by linarith)).prod
    (isFinitePLBallPair_Icc (show -d < d by linarith))
  obtain ⟨_, _, _, _, _, e, he, _⟩ := hrect
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := he
  have ht := (K.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hu := (K.affineOnFaces_affine
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hn := (K.affineOnFaces_affine
    (-ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have habs : FinitePiecewiseAffineOn (fun p : P2 => |p.2|) K.space :=
    (hu.max hn).congr (fun p _ => (abs_eq_max_neg (a := p.2)).symm)
  have hb := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ P2 b)).finitePiecewiseAffineOn hK
  have hh : FinitePiecewiseAffineOn (fun p : P2 => max |p.2| b) K.space := habs.max hb
  have h := (hu.prod_mk hh).prod_mk ht
  change FinitePiecewiseAffineOn (strip b true) K.space at h
  simpa only [hKs, rectangle] using h

theorem exists_reflection_resolving_annulus
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (reflectionTube L d))
    (hfib : ∀ z ∈ reflectionTube L d, ∀ w ∈ reflectionTube L d,
      τ z = τ w ↔
        (z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          (z.2 : AddCircle (4 * L)) = ((w.2 + 2 * L : ℝ) : AddCircle (4 * L)))) :
    ∃ (a : AddCircle (4 * L) × Icc (-d) d → X)
      (E : (AddCircle (4 * L) × Icc (-d) d) ≃ₜ squareAnnulus L d)
      (g : P2 → X),
      Topology.IsEmbedding a ∧
      Topology.IsEmbedding (fun x : squareAnnulus L d => g x) ∧
      PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      (∀ p, (E p : P2) = annulusMap L (by linarith) (p.1, p.2)) ∧
      (∀ p, g (E p) = a p) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a ((s : AddCircle (4 * L)), u) = τ ((u, max |(u : ℝ)| b), s)) ∧
      g '' squareAnnulus L d = τ '' (strip b true '' rectangle (4 * L) d) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) = τ ((-d, d), s) ∧
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), d)) = τ ((d, d), s)) ∧
      (∀ p : AddCircle (4 * L) × Icc (-d) d,
        a p ∈ τ '' reflectionTubeSide L d ↔ |(p.2 : ℝ)| = d) ∧
      (∀ x ∈ squareAnnulus L d, g x ∈ τ '' reflectionTubeSide L d ↔ |depth L x| = d) ∧
      squareAnnulus L d ∩ g ⁻¹' (τ '' reflectionTubeSide L d) =
        frontier (squareAnnulus L d) := by
  classical
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hmap : MapsTo (strip b true) (rectangle (4 * L) d) (reflectionTube L d) := by
    intro p hp
    change ((p.2 ∈ Icc (-d) d) ∧ max |p.2| b ∈ Icc (-d) d) ∧ p.1 ∈ Icc 0 (4 * L)
    exact ⟨⟨hp.2, ⟨by linarith [le_max_right |p.2| b],
      max_le (abs_le.mpr hp.2) hbd.le⟩⟩, hp.1⟩
  have hstrip := finitePL_upper_strip hL hd b
  have hstripcopy := hstrip
  obtain ⟨K, hK, hKs, _⟩ := hstripcopy
  have hstripK : FinitePiecewiseAffineOn (strip b true) K.space := by
    simpa only [hKs] using hstrip
  have hφ : PolyhedralPLInCharts e (τ ∘ strip b true) (rectangle (4 * L) d) := by
    have h := hτ.comp_finitePiecewiseAffineOn K hK hstripK (fun _ hx => hmap (hKs.subset hx))
    simpa only [hKs] using h
  have hend (u : Icc (-d) d) : τ (strip b true (0, u)) = τ (strip b true (4 * L, u)) := by
    apply (hfib _ (hmap ⟨⟨le_rfl, by positivity⟩, u.property⟩)
      _ (hmap ⟨⟨by positivity, le_rfl⟩, u.property⟩)).mpr
    exact Or.inl ⟨rfl, by simp only [strip, AddCircle.coe_zero, AddCircle.coe_period]⟩
  let a : AddCircle (4 * L) × Icc (-d) d → X := fun p =>
    AddCircle.liftIco (4 * L) 0 (fun s => τ (strip b true (s, p.2))) p.1
  have ha (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      a ((s : AddCircle (4 * L)), u) = τ (strip b true (s, u)) :=
    AddCircle.liftIco_zero_coe_apply_Icc (hend u) hs
  have hac : Continuous a := by
    apply AddCircle.continuous_parametric_liftIco
      (fun p : ℝ × Icc (-d) d => τ (strip b true (p.1, p.2)))
    exacts [hφ.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.property, p.2.property⟩), hend]
  have hrep (z : AddCircle (4 * L)) :
      ∃ s ∈ Icc 0 (4 * L), (s : AddCircle (4 * L)) = z := by
    exact ⟨AddCircle.equivIco (4 * L) 0 z,
      ⟨(AddCircle.equivIco (4 * L) 0 z).property.1,
        by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0 z).property.2.le⟩,
      AddCircle.coe_equivIco⟩
  have hai : Function.Injective a := by
    rintro ⟨z, u⟩ ⟨w, v⟩ heq
    obtain ⟨s, hs, rfl⟩ := hrep z
    obtain ⟨t, ht, rfl⟩ := hrep w
    rw [ha s hs u, ha t ht v] at heq
    rcases (hfib _ (hmap ⟨hs, u.property⟩) _ (hmap ⟨ht, v.property⟩)).mp heq with h | h
    · exact Prod.ext h.2 (Subtype.ext (congrArg Prod.fst h.1))
    · have he := congrArg Prod.snd h.1
      change max |(u : ℝ)| b = -max |(v : ℝ)| b at he
      linarith [le_max_right |(u : ℝ)| b, le_max_right |(v : ℝ)| b]
  have haem : Topology.IsEmbedding a := hac.isClosedEmbedding hai |>.isEmbedding
  obtain ⟨E, g, hE, hg, hgE, hgperiod, hgemb⟩ :=
    exists_square_annulus_map_of_period hcompat hd hwidth (τ ∘ strip b true) hφ a ha
  have hside (p : AddCircle (4 * L) × Icc (-d) d) :
      a p ∈ τ '' reflectionTubeSide L d ↔ |(p.2 : ℝ)| = d := by
    obtain ⟨s, hs, hz⟩ := hrep p.1
    obtain ⟨z, u⟩ := p
    dsimp at hz ⊢
    subst z
    rw [ha s hs u]
    constructor
    · rintro ⟨w, ⟨hw, hwside⟩, heq⟩
      have hcoords : |(u : ℝ)| = |w.1.1| ∧ max |(u : ℝ)| b = |w.1.2| := by
        rcases (hfib _ (hmap ⟨hs, u.property⟩) w hw).mp heq.symm with h | h
        · have hx := congrArg Prod.fst h.1
          have hy := congrArg Prod.snd h.1
          change (u : ℝ) = w.1.1 at hx
          change max |(u : ℝ)| b = w.1.2 at hy
          exact ⟨congrArg abs hx, by rw [← hy, abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]⟩
        · have hx := congrArg Prod.fst h.1
          have hy := congrArg Prod.snd h.1
          change (u : ℝ) = w.1.1 at hx
          change max |(u : ℝ)| b = -w.1.2 at hy
          exact ⟨congrArg abs hx, by
            have h := congrArg abs hy
            simpa only [abs_neg, abs_of_nonneg (le_max_of_le_left (abs_nonneg (u : ℝ)))] using h⟩
      rcases hwside with hx | hy
      · exact hcoords.1.trans hx
      · have hh := hcoords.2.trans hy
        rcases max_cases |(u : ℝ)| b with h | h
        · exact h.1.symm.trans hh
        · exact (ne_of_lt hbd (h.1.symm.trans hh)).elim
    · intro hu
      exact ⟨strip b true (s, u), ⟨hmap ⟨hs, u.property⟩, Or.inl hu⟩, rfl⟩
  have hgside (x : P2) (hx : x ∈ squareAnnulus L d) :
      g x ∈ τ '' reflectionTubeSide L d ↔ |depth L x| = d := by
    let p := E.symm ⟨x, hx⟩
    have hp : E p = ⟨x, hx⟩ := E.apply_symm_apply _
    have hv := hgE p
    rw [hp] at hv
    have hdepth : depth L x = (p.2 : ℝ) := by
      have h := depth_annulusMap hL
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr p.2.property) (by norm_num)) hwidth) p.1
      rw [← hE p, hp] at h
      exact h
    rw [hv, hdepth]
    exact hside p
  refine ⟨a, E, g, haem, hgemb haem, hg, hE, hgE, ha, ?_, ?_, hside, hgside, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let p := E.symm ⟨x, hx⟩
      obtain ⟨s, hs, hz⟩ := hrep p.1
      have hp : E p = ⟨x, hx⟩ := E.apply_symm_apply _
      refine ⟨strip b true (s, p.2), ⟨(s, p.2), ⟨hs, p.2.property⟩, rfl⟩, ?_⟩
      have he := hgE p
      rw [hp] at he
      rw [he]
      exact (ha s hs p.2).symm.trans (congrArg a (Prod.ext hz rfl))
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      let q : AddCircle (4 * L) × Icc (-d) d := ((p.1 : AddCircle (4 * L)), ⟨p.2, hp.2⟩)
      exact ⟨E q, (E q).property, (hgE q).trans (ha p.1 hp.1 q.2)⟩
  · intro s hs
    have hm := hgperiod s hs ⟨-d, ⟨le_rfl, by linarith⟩⟩
    have hp := hgperiod s hs ⟨d, ⟨by linarith, le_rfl⟩⟩
    simpa only [Function.comp_apply, strip, signedHeight, Bool.true_eq, if_true, height,
      abs_neg, abs_of_pos hd, max_eq_left hbd.le] using And.intro hm hp
  · have hclosed : IsClosed (squareAnnulus L d) :=
      (isClosed_Icc.prod isClosed_Icc).sdiff (isOpen_Ioo.prod isOpen_Ioo)
    ext x
    constructor
    · rintro ⟨hx, ht⟩
      exact (mem_frontier_squareAnnulus_iff hd (by linarith) hx).mpr ((hgside x hx).mp ht)
    · intro hx
      have ha := hclosed.closure_eq ▸ frontier_subset_closure hx
      exact ⟨ha, (hgside x ha).mpr ((mem_frontier_squareAnnulus_iff hd (by linarith) ha).mp hx)⟩

end Dehn
