import PoincareConjecture.Proofs.M76.Wall.InitialArcCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition









set_option autoImplicit false

open Set Geometry

namespace Geometry





theorem PolyhedralPLInCharts.exists_interior_chart_vectors
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X E} {f : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (B : OpenPartialHomeomorph X E)
    (hcompat : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E)
    (hxB : f a ∈ B.source) (hzero : B (f a) = 0) :
    ∃ u v : E, u ≠ 0 ∧ v ≠ 0 ∧ (∀ c : ℝ, 0 < c → u ≠ c • v) ∧
      ∃ δm ∈ Ioo (0 : ℝ) 1, ∃ δp ∈ Ioo (0 : ℝ) 1,
        MapsTo (fun t => f (a - a * t)) (Icc 0 δm) B.source ∧
        MapsTo (fun t => f (a + (1 - a) * t)) (Icc 0 δp) B.source ∧
        (∀ t ∈ Icc 0 δm, B (f (a - a * t)) = t • u) ∧
        ∀ t ∈ Icc 0 δp, B (f (a + (1 - a) * t)) = t • v := by
  let Am : ℝ →ᴬ[ℝ] ℝ :=
    ContinuousAffineMap.const ℝ ℝ a - a • ContinuousAffineMap.id ℝ ℝ
  let Ap : ℝ →ᴬ[ℝ] ℝ :=
    ContinuousAffineMap.const ℝ ℝ a + (1 - a) • ContinuousAffineMap.id ℝ ℝ
  have hAm : MapsTo Am (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    change a - a * t ∈ Icc (0 : ℝ) 1
    constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2]
  have hAp : MapsTo Ap (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    change a + (1 - a) * t ∈ Icc (0 : ℝ) 1
    constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  have hPL (A : ℝ →ᴬ[ℝ] ℝ) (hA : MapsTo A (Icc 0 1) (Icc 0 1)) :
      PolyhedralPLInCharts e (f ∘ A) (Icc (0 : ℝ) 1) := by
    rw [← hKs]
    exact hf.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine A).finitePiecewiseAffineOn hK)
      (fun _ ht => hA (hKs.subset ht))
  have him : InjOn (f ∘ Am) (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hi (hAm hs) (hAm ht) hst
    change a - a * s = a - a * t at heq
    exact (mul_left_cancel₀ ha.1.ne') (by linarith)
  have hip : InjOn (f ∘ Ap) (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have heq := hi (hAp hs) (hAp ht) hst
    change a + (1 - a) * s = a + (1 - a) * t at heq
    exact (mul_left_cancel₀ (sub_pos.mpr ha.2).ne') (by linarith)
  have hm0 : (f ∘ Am) 0 = f a := by
    change f (a - a * 0) = f a
    simp
  have hp0 : (f ∘ Ap) 0 = f a := by
    change f (a + (1 - a) * 0) = f a
    simp
  obtain ⟨u, hu, δm, hδm, hmapm, hformm⟩ :=
    (hPL Am hAm).exists_initial_chart_vector him B hcompat
      (by simpa only [hm0] using hxB) (by simpa only [hm0] using hzero)
  obtain ⟨v, hv, δp, hδp, hmapp, hformp⟩ :=
    (hPL Ap hAp).exists_initial_chart_vector hip B hcompat
      (by simpa only [hp0] using hxB) (by simpa only [hp0] using hzero)
  refine ⟨u, v, hu, hv, ?_, δm, hδm, δp, hδp, hmapm, hmapp, hformm, hformp⟩
  intro c hc huv
  let s : ℝ := min (δm / 2) (δp / (2 * c))
  have hs : 0 < s := lt_min (by linarith [hδm.1])
    (div_pos hδp.1 (mul_pos zero_lt_two hc))
  have hsm : s ≤ δm := (min_le_left _ _).trans (by linarith [hδm.1])
  have hsp : c * s ≤ δp := by
    have hraw : s ≤ δp / (2 * c) := min_le_right _ _
    have hbound := (le_div_iff₀ (mul_pos zero_lt_two hc)).mp hraw
    nlinarith [mul_pos hc hs]
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.le, hsm.trans hδm.2.le⟩
  have hcsI : c * s ∈ Icc (0 : ℝ) 1 :=
    ⟨(mul_pos hc hs).le, hsp.trans hδp.2.le⟩
  have hcoord : B ((f ∘ Am) s) = B ((f ∘ Ap) (c * s)) := by
    rw [hformm s ⟨hs.le, hsm⟩, hformp (c * s) ⟨(mul_pos hc hs).le, hsp⟩,
      huv, smul_smul, mul_comm s c]
  have heq := hi (hAm hsI) (hAp hcsI)
    (B.injOn (hmapm ⟨hs.le, hsm⟩) (hmapp ⟨(mul_pos hc hs).le, hsp⟩) hcoord)
  change a - a * s = a + (1 - a) * (c * s) at heq
  nlinarith [mul_pos ha.1 hs, mul_pos (sub_pos.mpr ha.2) (mul_pos hc hs)]

end Geometry
