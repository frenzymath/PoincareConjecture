import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ReflectionAnnulus
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut











set_option autoImplicit false

open Set Geometry

namespace Dehn

local notation "C3" => ((ℝ × ℝ) × ℝ)


def singleReflectionTube (L d : ℝ) : Set C3 :=
  (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc 0 (2 * L)


def singleReflectionTubeSide (L d : ℝ) : Set C3 :=
  {z | z ∈ singleReflectionTube L d ∧ (|z.1.1| = d ∨ |z.1.2| = d)}



def reflectionSecondHalf (L : ℝ) (z : C3) : C3 :=
  ((z.1.1, -z.1.2), z.2 - 2 * L)


noncomputable def doubledReflectionTubeMap {X : Type*} (L : ℝ) (τ : C3 → X) : C3 → X :=
  fun z => if z.2 ≤ 2 * L then τ z else τ (reflectionSecondHalf L z)

private theorem coe_eq_half_shift {L s t : ℝ} (hL : 0 < L)
    (hs : s ∈ Icc 0 (4 * L)) (ht : t ∈ Icc 0 (4 * L)) :
    (s : AddCircle (4 * L)) = ((t + 2 * L : ℝ) : AddCircle (4 * L)) ↔
      s = t + 2 * L ∨ s + 2 * L = t := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  by_cases h : t ≤ 2 * L
  · rw [AddCircle.coe_eq_coe_iff_eq_or_endpoints hs
      (show t + 2 * L ∈ Icc 0 (4 * L) from ⟨by linarith [ht.1], by linarith⟩)]
    constructor
    · rintro (he | ⟨he, he'⟩ | ⟨he, he'⟩)
      · exact Or.inl he
      · exact Or.inr (by linarith)
      · linarith [ht.1]
    · rintro (he | he)
      · exact Or.inl he
      · exact Or.inr (Or.inl ⟨by linarith [hs.1], by linarith [hs.1]⟩)
  · have hcoe : ((t + 2 * L : ℝ) : AddCircle (4 * L)) =
        ((t - 2 * L : ℝ) : AddCircle (4 * L)) := by
      convert AddCircle.coe_add_period (p := 4 * L) (t - 2 * L) using 1
      congr 1
      ring
    rw [hcoe, AddCircle.coe_eq_coe_iff_eq_or_endpoints hs
      (show t - 2 * L ∈ Icc 0 (4 * L) from ⟨by linarith, by linarith [ht.2]⟩)]
    constructor
    · rintro (he | ⟨he, he'⟩ | ⟨he, he'⟩)
      · exact Or.inr (by linarith)
      · linarith [ht.2]
      · linarith
    · rintro (he | he)
      · linarith [hs.2]
      · exact Or.inl (by linarith)



theorem doubledReflectionTubeMap_fibers
    {X : Type*} {L d : ℝ} (hL : 0 < L) (τ : C3 → X)
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0))))
    (z : C3) (hz : z ∈ reflectionTube L d)
    (w : C3) (hw : w ∈ reflectionTube L d) :
    doubledReflectionTubeMap L τ z = doubledReflectionTubeMap L τ w ↔
      (z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∨
      (z.1 = (w.1.1, -w.1.2) ∧
        (z.2 : AddCircle (4 * L)) = ((w.2 + 2 * L : ℝ) : AddCircle (4 * L))) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  rw [AddCircle.coe_eq_coe_iff_eq_or_endpoints hz.2 hw.2, coe_eq_half_shift hL hz.2 hw.2]
  have hfirst (v : C3) (hv : v ∈ reflectionTube L d) (hh : v.2 ≤ 2 * L) :
      v ∈ singleReflectionTube L d := ⟨hv.1, hv.2.1, hh⟩
  have hsecond (v : C3) (hv : v ∈ reflectionTube L d) (hh : ¬v.2 ≤ 2 * L) :
      reflectionSecondHalf L v ∈ singleReflectionTube L d := by
    change ((v.1.1 ∈ Icc (-d) d) ∧ -v.1.2 ∈ Icc (-d) d) ∧ v.2 - 2 * L ∈ Icc 0 (2 * L)
    exact ⟨⟨hv.1.1, ⟨by linarith [hv.1.2.2], by linarith [hv.1.2.1]⟩⟩,
      ⟨by linarith, by linarith [hv.2.2]⟩⟩
  have hz0 := hz.2.1
  have hz4 := hz.2.2
  have hw0 := hw.2.1
  have hw4 := hw.2.2
  by_cases hzhalf : z.2 ≤ 2 * L <;> by_cases hwhalf : w.2 ≤ 2 * L
  · simp only [doubledReflectionTubeMap, if_pos hzhalf, if_pos hwhalf]
    rw [hfib z (hfirst z hz hzhalf) w (hfirst w hw hwhalf)]
    clear hfib hfirst hsecond hz hw
    simp only [Prod.ext_iff]
    aesop (add safe (by linarith))
  · simp only [doubledReflectionTubeMap, if_pos hzhalf, if_neg hwhalf]
    rw [hfib z (hfirst z hz hzhalf) _ (hsecond w hw hwhalf)]
    clear hfib hfirst hsecond hz hw
    simp only [reflectionSecondHalf, Prod.ext_iff, neg_neg]
    aesop (add safe (by linarith))
  · simp only [doubledReflectionTubeMap, if_neg hzhalf, if_pos hwhalf]
    rw [hfib _ (hsecond z hz hzhalf) w (hfirst w hw hwhalf)]
    clear hfib hfirst hsecond hz hw
    simp only [reflectionSecondHalf, Prod.ext_iff, neg_neg, neg_eq_iff_eq_neg]
    aesop (add safe (by linarith))
  · simp only [doubledReflectionTubeMap, if_neg hzhalf, if_neg hwhalf]
    rw [hfib _ (hsecond z hz hzhalf) _ (hsecond w hw hwhalf)]
    clear hfib hfirst hsecond hz hw
    simp only [reflectionSecondHalf, Prod.ext_iff, neg_neg, neg_eq_iff_eq_neg]
    aesop (add safe (by linarith))



theorem doubledReflectionTubeMap_second
    {X : Type*} {L d : ℝ} (τ : C3 → X)
    (hseam : ∀ v ∈ Icc (-d) d ×ˢ Icc (-d) d,
      τ (v, 2 * L) = τ ((v.1, -v.2), 0))
    {z : C3} (hz : z ∈ (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (2 * L) (4 * L)) :
    doubledReflectionTubeMap L τ z = τ (reflectionSecondHalf L z) := by
  by_cases hh : z.2 ≤ 2 * L
  · have ht : z.2 = 2 * L := le_antisymm hh hz.2.1
    rw [doubledReflectionTubeMap, if_pos hh]
    have hzeta : z = (z.1, 2 * L) := Prod.ext rfl ht
    exact (congrArg τ hzeta).trans (by
      simpa only [reflectionSecondHalf, ht, sub_self] using hseam z.1 hz.1)
  · exact if_neg hh

private theorem reflection_box_triangulation {d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∃ K : SimplicialComplex ℝ C3, K.faces.Finite ∧
      K.space = (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc a b := by
  have hI := isFinitePLBallPair_Icc (show -d < d by linarith)
  have hbox := (hI.prod hI).prod (isFinitePLBallPair_Icc hab)
  obtain ⟨_, _, _, _, _, c, hc, _⟩ := hbox
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
  exact ⟨K, hK, hKs⟩

private noncomputable def reflectionSecondHalfAffine (L : ℝ) : C3 →ᴬ[ℝ] C3 :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    (-ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).prod
    ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ C3 (2 * L))



theorem doubledReflectionTubeMap_polyhedralPL
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hseam : ∀ v ∈ Icc (-d) d ×ˢ Icc (-d) d,
      τ (v, 2 * L) = τ ((v.1, -v.2), 0)) :
    PolyhedralPLInCharts e (doubledReflectionTubeMap L τ) (reflectionTube L d) := by
  obtain ⟨K₀, hK₀, hK₀s⟩ := reflection_box_triangulation hd (show (0 : ℝ) < 2 * L by linarith)
  obtain ⟨K₁, hK₁, hK₁s⟩ := reflection_box_triangulation hd (show 2 * L < 4 * L by linarith)
  have hzero : PolyhedralPLInCharts e (doubledReflectionTubeMap L τ) K₀.space := by
    rw [hK₀s]
    exact hτ.congr (fun z hz => (if_pos hz.2.2).symm)
  have hA : FinitePiecewiseAffineOn (reflectionSecondHalf L) K₁.space :=
    (K₁.affineOnFaces_affine (reflectionSecondHalfAffine L)).finitePiecewiseAffineOn hK₁
  have hmap : MapsTo (reflectionSecondHalf L) K₁.space (singleReflectionTube L d) := by
    intro z hz
    have hz := hK₁s.subset hz
    change ((z.1.1 ∈ Icc (-d) d) ∧ -z.1.2 ∈ Icc (-d) d) ∧ z.2 - 2 * L ∈ Icc 0 (2 * L)
    exact ⟨⟨hz.1.1, ⟨by linarith [hz.1.2.2], by linarith [hz.1.2.1]⟩⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hone : PolyhedralPLInCharts e (doubledReflectionTubeMap L τ) K₁.space :=
    (hτ.comp_finitePiecewiseAffineOn K₁ hK₁ hA hmap).congr
      (fun z hz => (doubledReflectionTubeMap_second τ hseam (hK₁s.subset hz)).symm)
  have hcover : K₀.space ∪ K₁.space = reflectionTube L d := by
    rw [hK₀s, hK₁s]
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
      · exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    · intro hz
      by_cases hh : z.2 ≤ 2 * L
      · exact Or.inl ⟨hz.1, hz.2.1, hh⟩
      · exact Or.inr ⟨hz.1, le_of_not_ge hh, hz.2.2⟩
  rw [← hcover]
  exact PolyhedralPLInCharts.union_of_finite hcompat K₀ K₁ hK₀ hK₁ hzero hone





theorem doubledReflectionTubeMap_spec
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0)))) :
    PolyhedralPLInCharts e (doubledReflectionTubeMap L τ) (reflectionTube L d) ∧
      EqOn (doubledReflectionTubeMap L τ) τ (singleReflectionTube L d) ∧
      (∀ z ∈ (Icc (-d) d ×ˢ Icc (-d) d) ×ˢ Icc (2 * L) (4 * L),
        doubledReflectionTubeMap L τ z = τ (reflectionSecondHalf L z)) ∧
      (∀ z ∈ reflectionTube L d, ∀ w ∈ reflectionTube L d,
        doubledReflectionTubeMap L τ z = doubledReflectionTubeMap L τ w ↔
          (z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∨
          (z.1 = (w.1.1, -w.1.2) ∧
            (z.2 : AddCircle (4 * L)) = ((w.2 + 2 * L : ℝ) : AddCircle (4 * L)))) ∧
      doubledReflectionTubeMap L τ '' reflectionTube L d = τ '' singleReflectionTube L d ∧
      doubledReflectionTubeMap L τ '' reflectionTubeSide L d =
        τ '' singleReflectionTubeSide L d := by
  have hseam (v : ℝ × ℝ) (hv : v ∈ Icc (-d) d ×ˢ Icc (-d) d) :
      τ (v, 2 * L) = τ ((v.1, -v.2), 0) := by
    apply (hfib (v, 2 * L) ⟨hv, by positivity, le_rfl⟩
      ((v.1, -v.2), 0) ⟨⟨hv.1, ⟨by linarith [hv.2.2], by linarith [hv.2.1]⟩⟩,
        le_rfl, by positivity⟩).mpr
    exact Or.inr ⟨by simp only [neg_neg, Prod.eta], Or.inr ⟨rfl, rfl⟩⟩
  have hfirst : EqOn (doubledReflectionTubeMap L τ) τ (singleReflectionTube L d) :=
    fun z hz => if_pos hz.2.2
  have hsubset : singleReflectionTube L d ⊆ reflectionTube L d :=
    fun z hz => ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  have hsecond (z : C3) (hz : z ∈ reflectionTube L d) (hh : ¬z.2 ≤ 2 * L) :
      reflectionSecondHalf L z ∈ singleReflectionTube L d := by
    change ((z.1.1 ∈ Icc (-d) d) ∧ -z.1.2 ∈ Icc (-d) d) ∧ z.2 - 2 * L ∈ Icc 0 (2 * L)
    exact ⟨⟨hz.1.1, ⟨by linarith [hz.1.2.2], by linarith [hz.1.2.1]⟩⟩,
      ⟨by linarith, by linarith [hz.2.2]⟩⟩
  refine ⟨doubledReflectionTubeMap_polyhedralPL hcompat hL hd τ hτ hseam,
    hfirst, fun _ hz => doubledReflectionTubeMap_second τ hseam hz,
    doubledReflectionTubeMap_fibers hL τ hfib, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hh : z.2 ≤ 2 * L
      · exact ⟨z, ⟨hz.1, hz.2.1, hh⟩, (if_pos hh).symm⟩
      · exact ⟨reflectionSecondHalf L z, hsecond z hz hh, (if_neg hh).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hsubset hz, hfirst hz⟩
  · ext y
    constructor
    · rintro ⟨z, ⟨hz, hside⟩, rfl⟩
      by_cases hh : z.2 ≤ 2 * L
      · exact ⟨z, ⟨⟨hz.1, hz.2.1, hh⟩, hside⟩, (if_pos hh).symm⟩
      · refine ⟨reflectionSecondHalf L z, ⟨hsecond z hz hh, ?_⟩, (if_neg hh).symm⟩
        simpa only [reflectionSecondHalf, abs_neg] using hside
    · rintro ⟨z, ⟨hz, hside⟩, rfl⟩
      exact ⟨z, ⟨hsubset hz, hside⟩, hfirst hz⟩

end Dehn
