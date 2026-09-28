import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.PeriodicDescent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CutRectangleQuotient
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "p0" => (4 * (8 : ℝ))
local notation "Circle" => AddCircle p0
local notation "Rect" => rectangle p0 1
local notation "I" => unitInterval

theorem exists_joint_PL_annulus_family_of_cut_rectangle
    (H : I → Rect ≃ₜ Rect)
    (F Fi : (ℝ × P2) → P2)
    (hF : FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Rect))
    (hFi : FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Rect))
    (hFval : ∀ t : I, ∀ x : Rect, F (t, x) = (H t x : P2))
    (hFival : ∀ t : I, ∀ x : Rect, Fi (t, x) = ((H t).symm x : P2))
    (hfix : ∀ t : I, ∀ x : Rect,
      (x : P2).1 = 0 ∨ (x : P2).1 = p0 ∨ (x : P2).2 = -1 ∨ (x : P2).2 = 1 → H t x = x) :
    ∃ (A : I → Ann ≃ₜ Ann) (g gi : (ℝ × P2) → P2),
      FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn gi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, g (t, x) = (A t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, gi (t, x) = ((A t).symm x : P2)) ∧
      Continuous (fun p : I × Ann => A p.1 p.2) ∧
      Continuous (fun p : I × Ann => (A p.1).symm p.2) ∧
      (∀ (t : I) (side : Bool) z, A t (annulusRimPoint side z) = annulusRimPoint side z) ∧
      ∀ (t : I) (s : ℝ) (hs : s ∈ Icc 0 p0) (u : Icc (-1 : ℝ) 1),
        (A t ⟨annulusMap 8 (by norm_num) ((s : Circle), u),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : P2) =
        annulusMap 8 (by norm_num)
          (((H t ⟨(s, u), hs, u.property⟩ : P2).1 : Circle),
            (H t ⟨(s, u), hs, u.property⟩ : P2).2) := by
  classical
  let : Fact (0 < p0) := ⟨by norm_num⟩
  have hrect : ∃ K : SimplicialComplex ℝ P2, K.faces.Finite ∧ K.space = Rect := by
    obtain ⟨c, ⟨f, hf, _⟩, _⟩ := exists_rotated_strip_charts
      (L := p0) (d := 1) (by norm_num) (by norm_num) (0 : Fin 4)
    obtain ⟨K, hK, hKs, _⟩ := hf
    exact ⟨K, hK, hKs⟩
  obtain ⟨K, hK, hKs⟩ := hrect
  have hHt (t : I) : (H t).IsFinitePL := by
    let j : P2 →ᴬ[ℝ] ℝ × P2 :=
      (ContinuousAffineMap.const ℝ P2 (t : ℝ)).prod (ContinuousAffineMap.id ℝ P2)
    have hj : FinitePiecewiseAffineOn j Rect := by
      rw [← hKs]
      exact (K.affineOnFaces_affine j).finitePiecewiseAffineOn hK
    exact ⟨fun x => F (t, x), hF.comp hj (fun x hx => ⟨t.property, hx⟩),
      fun x => (hFval t x).symm⟩
  have hA (t : I) := exists_annulus_homeomorph_of_cut_rectangle
    (L := 8) (d := 1) (by norm_num) (by norm_num) (H t) (hHt t)
    (fun u => congrArg Subtype.val (hfix t _ (Or.inl rfl)))
    (fun u => congrArg Subtype.val (hfix t _ (Or.inr (Or.inl rfl))))
  choose A hAPL hperiod using hA
  let g : (ℝ × P2) → P2 := fun p =>
    if ht : p.1 ∈ Icc (0 : ℝ) 1 then
      if hx : p.2 ∈ Ann then A ⟨p.1, ht⟩ ⟨p.2, hx⟩ else 0
    else 0
  let gi : (ℝ × P2) → P2 := fun p =>
    if ht : p.1 ∈ Icc (0 : ℝ) 1 then
      if hx : p.2 ∈ Ann then (A ⟨p.1, ht⟩).symm ⟨p.2, hx⟩ else 0
    else 0
  have hgval (t : I) (x : Ann) : g (t, x) = (A t x : P2) := by
    simp only [g, dif_pos t.property, dif_pos x.property]
  have hgival (t : I) (x : Ann) : gi (t, x) = ((A t).symm x : P2) := by
    simp only [gi, dif_pos t.property, dif_pos x.property]
  let Q : P2 → P2 := fun x => annulusMap 8 (by norm_num) ((x.1 : Circle), x.2)
  have hQ : FinitePiecewiseAffineOn Q Rect := by
    simpa only [Q, rectangle, zero_add] using finitePiecewiseAffineOn_annulusMap_period
      (L := 8) (d := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
      (AddCircle.coe_zero _)
  have hmapF : MapsTo F (Icc (0 : ℝ) 1 ×ˢ Rect) Rect := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [hFval ⟨t, ht⟩ ⟨x, hx⟩]
    exact (H ⟨t, ht⟩ ⟨x, hx⟩).property
  have hmapFi : MapsTo Fi (Icc (0 : ℝ) 1 ×ˢ Rect) Rect := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [hFival ⟨t, ht⟩ ⟨x, hx⟩]
    exact ((H ⟨t, ht⟩).symm ⟨x, hx⟩).property
  have hg : FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ Ann) := by
    apply finitePL_annulus_track_of_period (by norm_num) (by norm_num)
      (Q ∘ F) g (hQ.comp hF hmapF)
    intro t ht s hs u
    rw [hgval ⟨t, ht⟩ ⟨_, _root_.Dehn.annulus_period_point_mem
      (by norm_num) (by norm_num) _ u⟩, hperiod ⟨t, ht⟩ s hs u, Function.comp_apply,
      hFval ⟨t, ht⟩ ⟨(s, u), hs, u.property⟩]
  have hiperiod (t : I) (s : ℝ) (hs : s ∈ Icc 0 p0) (u : Icc (-1 : ℝ) 1) :
      ((A t).symm ⟨Q (s, u), _root_.Dehn.annulus_period_point_mem
        (by norm_num) (by norm_num) _ u⟩ : P2) =
      Q ((H t).symm ⟨(s, u), hs, u.property⟩) := by
    let y : Rect := (H t).symm ⟨(s, u), hs, u.property⟩
    have hy : Q y ∈ Ann := _root_.Dehn.annulus_period_point_mem
      (by norm_num) (by norm_num) _ ⟨(y : P2).2, y.property.2⟩
    have hv : A t ⟨Q y, hy⟩ = ⟨Q (s, u), _root_.Dehn.annulus_period_point_mem
        (by norm_num) (by norm_num) _ u⟩ := by
      apply Subtype.ext
      rw [hperiod t (y : P2).1 y.property.1 ⟨(y : P2).2, y.property.2⟩]
      change Q (H t y) = Q (s, u)
      rw [(H t).apply_symm_apply]
    exact congrArg Subtype.val ((A t).symm_apply_eq.mpr hv.symm)
  have hgi : FinitePiecewiseAffineOn gi (Icc (0 : ℝ) 1 ×ˢ Ann) := by
    apply finitePL_annulus_track_of_period (by norm_num) (by norm_num)
      (Q ∘ Fi) gi (hQ.comp hFi hmapFi)
    intro t ht s hs u
    rw [hgival ⟨t, ht⟩ ⟨_, _root_.Dehn.annulus_period_point_mem
      (by norm_num) (by norm_num) _ u⟩, hiperiod ⟨t, ht⟩ s hs u, Function.comp_apply,
      hFival ⟨t, ht⟩ ⟨(s, u), hs, u.property⟩]
  have hcg : Continuous (fun p : I × Ann => g ((p.1 : ℝ), (p.2 : P2))) :=
    hg.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.property, p.2.property⟩)
  have hcgi : Continuous (fun p : I × Ann => gi ((p.1 : ℝ), (p.2 : P2))) :=
    hgi.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.property, p.2.property⟩)
  refine ⟨A, g, gi, hg, hgi, hgval, hgival,
    continuous_induced_rng.mpr (hcg.congr (fun p => hgval p.1 p.2)),
    continuous_induced_rng.mpr (hcgi.congr (fun p => hgival p.1 p.2)), ?_, hperiod⟩
  intro t side z
  let s : ℝ := AddCircle.equivIco p0 0 z
  have hs : s ∈ Icc 0 p0 := ⟨(AddCircle.equivIco _ _ z).property.1,
    by simpa using (AddCircle.equivIco p0 0 z).property.2.le⟩
  have hz : (s : Circle) = z := AddCircle.coe_equivIco
  cases side
  · have hh := hperiod t s hs ⟨-1, by norm_num⟩
    rw [hfix t _ (Or.inr (Or.inr (Or.inl rfl)))] at hh
    apply Subtype.ext
    simpa only [annulusRimPoint, Bool.false_eq_true, ↓reduceIte, ← hz] using hh
  · have hh := hperiod t s hs ⟨1, by norm_num⟩
    rw [hfix t _ (Or.inr (Or.inr (Or.inr rfl)))] at hh
    apply Subtype.ext
    simpa only [annulusRimPoint, ↓reduceIte, ← hz] using hh

end PoincareConjecture.M76.Dehn
