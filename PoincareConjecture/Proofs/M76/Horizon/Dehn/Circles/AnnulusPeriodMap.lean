import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

theorem exists_square_annulus_map_of_period
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (φ : (ℝ × ℝ) → X) (hφ : PolyhedralPLInCharts e φ (rectangle (4 * L) d))
    (a : AddCircle (4 * L) × Icc (-d) d → X)
    (ha : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (t : Icc (-d) d),
      a ((s : AddCircle (4 * L)), t) = φ (s, t)) :
    ∃ (E : (AddCircle (4 * L) × Icc (-d) d) ≃ₜ squareAnnulus L d)
      (g : (ℝ × ℝ) → X),
      (∀ p, (E p : ℝ × ℝ) = annulusMap L (by linarith) (p.1, p.2)) ∧
      PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      (∀ p, g (E p) = a p) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (t : Icc (-d) d),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), t)) = φ (s, t)) ∧
      (Topology.IsEmbedding a → Topology.IsEmbedding (fun x : squareAnnulus L d => g x)) := by
  classical
  have hL : 0 < L := by linarith
  obtain ⟨E, hE⟩ := exists_annulus_homeomorph hL hd.le hwidth
  let g : (ℝ × ℝ) → X := fun x =>
    if hx : x ∈ squareAnnulus L d then a (E.symm ⟨x, hx⟩) else φ (0, 0)
  have hg (x : squareAnnulus L d) : g x = a (E.symm x) := by simp only [g, dif_pos x.property]
  have hgE (p : AddCircle (4 * L) × Icc (-d) d) : g (E p) = a p := by
    rw [hg, E.symm_apply_apply]
  have hperiod (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (t : Icc (-d) d) :
      g (annulusMap L hL ((s : AddCircle (4 * L)), t)) = φ (s, t) := by
    rw [← hE (((s : AddCircle (4 * L)), t)), hgE, ha s hs t]
  have hpieces (i : Fin 4) : ∃ K : SimplicialComplex ℝ (ℝ × ℝ),
      K.faces.Finite ∧ K.space = stripRegion L d i ∧ PolyhedralPLInCharts e g K.space := by
    obtain ⟨c, hc, hcv⟩ := exists_rotated_strip_charts hd hwidth i
    obtain ⟨r, hr, hrv⟩ := hc.symm
    have hrcopy := hr
    obtain ⟨K, hK, hKs, _⟩ := hrcopy
    let A : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
      ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) ((i.val : ℝ) * L, 0)
    have hrK : FinitePiecewiseAffineOn r K.space := by simpa only [hKs] using hr
    have hAr : FinitePiecewiseAffineOn (A ∘ r) K.space := hrK.postcomp A.toContinuousAffineMap
    have hmap : MapsTo (A ∘ r) K.space (rectangle (4 * L) d) := by
      intro x hx
      have hp : r x ∈ rectangle L d := by
        rw [← hrv ⟨x, hKs.subset hx⟩]
        exact (c.symm ⟨x, hKs.subset hx⟩).property
      change ((i.val : ℝ) * L + (r x).1 ∈ Icc 0 (4 * L)) ∧
        0 + (r x).2 ∈ Icc (-d) d
      refine ⟨?_, by simpa only [zero_add] using hp.2⟩
      fin_cases i <;> norm_num <;> constructor <;> linarith [hp.1.1, hp.1.2]
    refine ⟨K, hK, hKs, (hφ.comp_finitePiecewiseAffineOn K hK hAr hmap).congr ?_⟩
    intro x hx
    let p : rectangle L d := c.symm ⟨x, hKs.subset hx⟩
    have hrp : r x = p := (hrv ⟨x, hKs.subset hx⟩).symm
    have hcp : (c p : ℝ × ℝ) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have ht : 4 * |(p : ℝ × ℝ).2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr p.property.2) (by norm_num)) hwidth
    have hs : (p : ℝ × ℝ).1 + (i.val : ℝ) * L ∈ Icc 0 (4 * L) := by
      have h := (hmap hx).1
      change (i.val : ℝ) * L + (r x).1 ∈ Icc 0 (4 * L) at h
      simpa only [hrp, add_comm] using h
    have hpoint : annulusMap L hL
        ((((p : ℝ × ℝ).1 + (i.val : ℝ) * L : ℝ) : AddCircle (4 * L)),
          (p : ℝ × ℝ).2) = x := by
      rw [annulusMap_coe hL ht hs, wrappedStripMap_block ht p.property.1 i, ← hcv p, hcp]
    have hval := hperiod _ hs ⟨(p : ℝ × ℝ).2, p.property.2⟩
    rw [hpoint] at hval
    change φ ((i.val : ℝ) * L + (r x).1, 0 + (r x).2) = g x
    simpa only [hrp, zero_add, add_comm] using hval.symm
  choose K hK hKs hgK using hpieces
  obtain ⟨K01, hK01, hK01s⟩ := (K 0).exists_finite_triangulation_union (K 1) (hK 0) (hK 1)
  have hg01 : PolyhedralPLInCharts e g K01.space := by
    rw [hK01s]
    exact PolyhedralPLInCharts.union_of_finite hcompat (K 0) (K 1) (hK 0) (hK 1) (hgK 0) (hgK 1)
  obtain ⟨K012, hK012, hK012s⟩ := K01.exists_finite_triangulation_union (K 2) hK01 (hK 2)
  have hg012 : PolyhedralPLInCharts e g K012.space := by
    rw [hK012s]
    exact PolyhedralPLInCharts.union_of_finite hcompat K01 (K 2) hK01 (hK 2) hg01 (hgK 2)
  have hall := PolyhedralPLInCharts.union_of_finite hcompat K012 (K 3) hK012 (hK 3) hg012 (hgK 3)
  have hwhole : K012.space ∪ (K 3).space = squareAnnulus L d := by
    rw [hK012s, hK01s, hKs 0, hKs 1, hKs 2, hKs 3]
    exact union_four_strips hd.le (by linarith)
  refine ⟨E, g, hE, by simpa only [hwhole] using hall, hgE, hperiod, ?_⟩
  intro ha
  have hfun : (fun x : squareAnnulus L d => g x) = a ∘ E.symm := funext hg
  rw [hfun]
  exact ha.comp E.symm.isEmbedding

end Dehn
