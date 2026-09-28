import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Mathlib.CenteredTorusSquareChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.exists_original_coordinate_crossing_patch
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K) {S : Set X}
    (H : K.space ≃ₜ S) (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z)) :
    ∃ u : P2 → X,
      PolyhedralPLInCharts e u (Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4)) ∧
      InjOn u (Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4)) ∧
      MapsTo u (Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4)) S ∧
      u 0 = (h (((p / 2 : ℝ) : AddCircle p), ((p / 2 : ℝ) : AddCircle p)) : X) ∧
      (∀ z ∈ Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4),
        u z = (h (AddCircle.centeredSquareQuotient p z) : X)) ∧
      (∀ z ∈ Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4),
        u z ∈ range (fun t : AddCircle p => (h (t, ((p / 2 : ℝ) : AddCircle p)) : X)) ↔ z.2 = 0) ∧
      ∀ z ∈ Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4),
        u z ∈ range (fun t : AddCircle p => (h (((p / 2 : ℝ) : AddCircle p), t) : X)) ↔ z.1 = 0 := by
  have hp : 0 < p := Fact.out
  obtain ⟨m, hm, hmval⟩ := M.finite_piecewise_affine
  obtain ⟨J, hJ, hJs, hJm⟩ := hm
  have hmap : MapsTo m J.space K.space := by
    intro z hz
    have hzsq := hJs.subset hz
    rw [hmval (⟨z.1, hzsq.1⟩, ⟨z.2, hzsq.2⟩)]
    exact (M.map _).property
  have hFm : PolyhedralPLInCharts e (F ∘ m) (squareCarrier p) :=
    hJs ▸ hF.comp_finitePiecewiseAffineOn J hJ ⟨J, hJ, rfl, hJm⟩ hmap
  let shift := ContinuousAffineEquiv.constVAdd ℝ P2 (p / 2, p / 2)
  let A := Icc (-p / 4) (p / 4) ×ˢ Icc (-p / 4) (p / 4)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨D, hD, hDs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show -p / 4 < p / 4 by linarith)).prod
      (isFinitePLBallPair_Icc (show -p / 4 < p / 4 by linarith))
  have hshift : MapsTo shift A (squareCarrier p) := by
    intro z hz
    change (0 ≤ p / 2 + z.1 ∧ p / 2 + z.1 ≤ p) ∧
      (0 ≤ p / 2 + z.2 ∧ p / 2 + z.2 ≤ p)
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  let u := F ∘ m ∘ shift
  have hu : PolyhedralPLInCharts e u A := by
    dsimp only [A]
    rw [← hDs]
    exact hFm.comp_finitePiecewiseAffineOn D hD
      ((D.affineOnFaces_affine shift.toContinuousAffineMap).finitePiecewiseAffineOn hD)
      (fun _ hz => hshift (hDs.subset hz))
  have huv (z : P2) (hz : z ∈ A) : u z = (h (AddCircle.centeredSquareQuotient p z) : X) := by
    have hzs := hshift hz
    let w : Square p := (⟨p / 2 + z.1, hzs.1⟩, ⟨p / 2 + z.2, hzs.2⟩)
    change F (m (p / 2 + z.1, p / 2 + z.2)) = _
    rw [hmval w, hFval, ← hvalue w]
    rfl
  have hsource (z : P2) (hz : z ∈ A) : z ∈ (AddCircle.centeredSquareQuotient p).source := by
    rw [AddCircle.centeredSquareQuotient_source, mem_ofPred_eq, Prod.norm_def,
      Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff, abs_lt, abs_lt]
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hzero : (0 : P2) ∈ A := by
    change (-p / 4 ≤ 0 ∧ 0 ≤ p / 4) ∧ (-p / 4 ≤ 0 ∧ 0 ≤ p / 4)
    constructor <;> constructor <;> linarith
  have hcoef {t : ℝ} (ht : t ∈ Icc (-p / 4) (p / 4)) :
      (((p / 2 + t : ℝ) : AddCircle p) = ((p / 2 : ℝ) : AddCircle p)) ↔ t = 0 := by
    rw [AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
      (show p / 2 + t ∈ Ico 0 (0 + p) by constructor <;> linarith [ht.1, ht.2])
      (show p / 2 ∈ Ico 0 (0 + p) by constructor <;> linarith)]
    constructor <;> intro ht' <;> linarith
  refine ⟨u, hu, ?_, ?_, ?_, huv, ?_, ?_⟩
  · intro z hz w hw heq
    rw [huv z hz, huv w hw] at heq
    exact (AddCircle.centeredSquareQuotient p).injOn (hsource z hz) (hsource w hw)
      (h.injective (Subtype.ext heq))
  · intro z hz
    rw [huv z hz]
    exact (h _).property
  · simpa only [AddCircle.centeredSquareQuotient_apply, Prod.fst_zero, Prod.snd_zero, add_zero]
      using huv 0 hzero
  · intro z hz
    rw [huv z hz, AddCircle.centeredSquareQuotient_apply]
    constructor
    · rintro ⟨t, ht⟩
      exact (hcoef hz.2).mp (congrArg Prod.snd (h.injective (Subtype.ext ht))).symm
    · intro ht
      refine ⟨((p / 2 + z.1 : ℝ) : AddCircle p), ?_⟩
      rw [ht, add_zero]
  · intro z hz
    rw [huv z hz, AddCircle.centeredSquareQuotient_apply]
    constructor
    · rintro ⟨t, ht⟩
      exact (hcoef hz.1).mp (congrArg Prod.fst (h.injective (Subtype.ext ht))).symm
    · intro ht
      refine ⟨((p / 2 + z.2 : ℝ) : AddCircle p), ?_⟩
      rw [ht, add_zero]

end PoincareConjecture.M76.PeriodicSquare
