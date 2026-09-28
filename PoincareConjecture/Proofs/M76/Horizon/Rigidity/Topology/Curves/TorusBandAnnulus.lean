import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.SourceTorusBand
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFinitePL









set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Rect" => rectangle (4 * (8 : ℝ)) 1

theorem exists_finitePL_annulus_of_circle_band
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (b : C(AddCircle p × Icc (-r) r, E)) (hb : IsEmbedding b)
    (u : P2 → E) (hu : FinitePiecewiseAffineOn u (Icc 0 p ×ˢ Icc (-r) r))
    (hvalue : ∀ s : Icc 0 p, ∀ t : Icc (-r) r, u (s, t) = b ((s : ℝ), t)) :
    ∃ A : Ann ≃ₜ range b,
      A.IsFinitePL ∧ A.symm.IsFinitePL ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * (8 : ℝ))) (t : Icc (-1 : ℝ) 1),
        (A ⟨annulusMap 8 (by norm_num) ((s : Circle), t),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ t⟩ : E) =
          b ((((32 : ℝ)⁻¹ * p * s : ℝ) : AddCircle p),
            ⟨r * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩)) ∧
      ∀ z : Ann,
        (A z : E) ∈ b '' {x | -r < (x.2 : ℝ) ∧ (x.2 : ℝ) < r} ↔
          -1 < depth 8 (z : P2) ∧ depth 8 (z : P2) < 1 := by
  classical
  let : Fact (0 < p) := ⟨hp⟩
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num) hp.ne'
  let C : P2 →ᴬ[ℝ] P2 :=
    (((32 : ℝ)⁻¹ * p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
      (r • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)
  have hC (z : P2) : C z = ((32 : ℝ)⁻¹ * p * z.1, r * z.2) := rfl
  have hmaps : MapsTo C Rect (Icc 0 p ×ˢ Icc (-r) r) := by
    intro z hz
    change z ∈ Icc (0 : ℝ) (4 * (8 : ℝ)) ×ˢ Icc (-1 : ℝ) 1 at hz
    rw [hC]
    constructor
    · constructor <;> norm_num <;> nlinarith [hz.1.1, hz.1.2]
    · constructor <;> nlinarith [hz.2.1, hz.2.2]
  have hCPL : FinitePiecewiseAffineOn C Rect := by
    obtain ⟨K, hK, hKs, _⟩ := finitePiecewiseAffineOn_wrappedStripMap
      (L := 8) (d := 1) (by norm_num) (by norm_num)
    exact ⟨K, hK, hKs, K.affineOnFaces_affine C⟩
  let v := u ∘ C
  have hv : FinitePiecewiseAffineOn v Rect := hu.comp hCPL hmaps
  have hvvalue (s : ℝ) (hs : s ∈ Icc 0 (4 * (8 : ℝ))) (t : Icc (-1 : ℝ) 1) :
      v (s, t) = b (scale (s : Circle),
        ⟨r * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩) := by
    have hm := hmaps (show (s, (t : ℝ)) ∈ Rect from ⟨hs, t.property⟩)
    have hv0 := hvalue ⟨(C (s, t)).1, hm.1⟩ ⟨(C (s, t)).2, hm.2⟩
    dsimp only [v, Function.comp_apply]
    rw [← Prod.eta (C (s, t))]
    rw [hv0]
    congr 2
    change (((32 : ℝ)⁻¹ * p * s : ℝ) : AddCircle p) =
      ((s * ((4 * (8 : ℝ))⁻¹ * p) : ℝ) : AddCircle p)
    congr 1
    ring
  have hfib : ∀ x ∈ Rect, ∀ y ∈ Rect,
      v x = v y ↔ x.2 = y.2 ∧ (x.1 : Circle) = (y.1 : Circle) := by
    intro x hx y hy
    rw [hvvalue x.1 hx.1 ⟨x.2, hx.2⟩, hvvalue y.1 hy.1 ⟨y.2, hy.2⟩]
    constructor
    · intro heq
      have h := hb.injective heq
      exact ⟨mul_left_cancel₀ hr.ne' (congrArg (fun z => (z.2 : ℝ)) h),
        scale.injective (congrArg Prod.fst h)⟩
    · rintro ⟨ht, hs⟩
      congr 1
      exact Prod.ext (congrArg scale hs) (Subtype.ext (congrArg (fun t => r * t) ht))
  have himage : v '' Rect = range b := by
    ext y
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
      exact ⟨_, (hvvalue s hs ⟨t, ht⟩).symm⟩
    · rintro ⟨⟨z, t⟩, rfl⟩
      let s := AddCircle.equivIco (4 * (8 : ℝ)) 0 (scale.symm z)
      have hs : (s : ℝ) ∈ Icc 0 (4 * (8 : ℝ)) := ⟨s.property.1, by simpa using s.property.2.le⟩
      have hsz : scale ((s : ℝ) : Circle) = z := by
        rw [show ((s : ℝ) : Circle) = scale.symm z from AddCircle.coe_equivIco,
          scale.apply_symm_apply]
      have ht : (t : ℝ) / r ∈ Icc (-1 : ℝ) 1 := by
        constructor
        · apply (le_div_iff₀ hr).mpr
          nlinarith [t.property.1]
        · apply (div_le_iff₀ hr).mpr
          nlinarith [t.property.2]
      refine ⟨((s : ℝ), (t : ℝ) / r), ⟨hs, ht⟩, ?_⟩
      rw [hvvalue (s : ℝ) hs ⟨(t : ℝ) / r, ht⟩, hsz]
      congr 2
      apply Subtype.ext
      exact mul_div_cancel₀ _ hr.ne'
  obtain ⟨A, hA, _, hperiod, hpoint⟩ := _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
    (L := 8) (d := 1) (by norm_num) (by norm_num) v hv hfib
  let A' := A.trans (Homeomorph.setCongr himage)
  have hA' : A'.IsFinitePL := hA.setCongr rfl himage
  refine ⟨A', hA', hA'.symm, ?_, ?_⟩
  · intro s hs t
    exact (hperiod s hs t).trans ((hvvalue s hs t).trans (by
      congr 2
      change ((s * ((4 * (8 : ℝ))⁻¹ * p) : ℝ) : AddCircle p) =
        ((((32 : ℝ)⁻¹ * p * s : ℝ)) : AddCircle p)
      congr 1
      ring))
  · intro z
    obtain ⟨s, hs, hsz⟩ := exists_period_parameter_of_depth
      (L := 8) (d := 1) (by norm_num) (by norm_num) z
    have hd := mem_squareAnnulus_iff_depth.mp z.property
    have hz : (A' z : E) = b (scale (s : Circle),
        ⟨r * depth 8 (z : P2), by constructor <;> nlinarith [hd.1, hd.2]⟩) :=
      (hpoint z s hs hsz).trans (hvvalue s hs ⟨depth 8 (z : P2), hd⟩)
    rw [hz]
    constructor
    · rintro ⟨x, hx, heq⟩
      have ht := congrArg (fun y => (y.2 : ℝ)) (hb.injective heq)
      constructor <;> nlinarith [hx.1, hx.2]
    · intro hz
      exact ⟨_, ⟨by nlinarith [hz.1], by nlinarith [hz.2]⟩, rfl⟩

namespace PeriodicSquare



theorem SourceSquareMap.exists_finitePL_coordinate_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K)
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
      (b : C(AddCircle p × Icc (-r) r, K.space))
      (A : Ann ≃ₜ range (fun z => (b z : E))),
      (∀ z : Square p, h (projection p z) = M.map z) ∧
      IsEmbedding b ∧
      (∀ z, b z = h (z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p))) ∧
      A.IsFinitePL ∧ A.symm.IsFinitePL ∧
      IsOpen (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * (8 : ℝ))) (t : Icc (-1 : ℝ) 1),
        (A ⟨annulusMap 8 (by norm_num) ((s : Circle), t),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ t⟩ : E) =
          (b ((((32 : ℝ)⁻¹ * p * s : ℝ) : AddCircle p),
            ⟨r * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩) : E)) ∧
      (∀ z : Ann,
        (A z : E) ∈ (fun x => (b x : E)) '' {x | -r < (x.2 : ℝ) ∧ (x.2 : ℝ) < r} ↔
          -1 < depth 8 (z : P2) ∧ depth 8 (z : P2) < 1) ∧
      ∃ retract : C(K.space, AddCircle p), ∀ z, retract (b z) = z.1 := by
  obtain ⟨h, b, u, hval, hb, hbval, hopen, hu, huval, retract, hretract⟩ :=
    M.exists_coordinate_band hr hwidth
  let bE : C(AddCircle p × Icc (-r) r, E) :=
    ⟨fun z => (b z : E), continuous_subtype_val.comp b.continuous⟩
  obtain ⟨A, hA, hAinv, hperiod, hinterior⟩ :=
    exists_finitePL_annulus_of_circle_band (Fact.out : (0 : ℝ) < p) hr bE
      (IsEmbedding.subtypeVal.comp hb) u hu huval
  exact ⟨h, b, A, hval, hb, hbval, hA, hAinv, hopen, hperiod, hinterior,
    retract, hretract⟩

end PeriodicSquare

end PoincareConjecture.M76
