import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.PositiveAnchors








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)


def coordinateSwap : E2 ≃ₗᵢ[Real] E2 where
  toFun := saddleCoordinateSwap
  invFun := saddleCoordinateSwap
  left_inv := saddleCoordinateSwap_swap
  right_inv := saddleCoordinateSwap_swap
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c x := by ext i; fin_cases i <;> rfl
  norm_map' x := by
    change ‖saddleCoordinateSwap x‖ = ‖x‖
    have h1 := EuclideanSpace.real_norm_sq_eq x
    have h2 := EuclideanSpace.real_norm_sq_eq (saddleCoordinateSwap x)
    simp only [Fin.sum_univ_two, saddleCoordinateSwap_zero, saddleCoordinateSwap_one] at h1 h2
    nlinarith [norm_nonneg x, norm_nonneg (saddleCoordinateSwap x)]


def stripReflection : Diffeomorph IR2 IR2 (Real × Real) (Real × Real) ∞ where
  toFun z := (z.1, -z.2)
  invFun z := (z.1, -z.2)
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := (contDiff_fst.prodMk contDiff_snd.neg).contMDiff
  contMDiff_invFun := (contDiff_fst.prodMk contDiff_snd.neg).contMDiff

def reflectedChart (e : OpenPartialHomeomorph E2 S2) : OpenPartialHomeomorph E2 S2 :=
  coordinateSwap.toHomeomorph.toOpenPartialHomeomorph.trans e

def reflectedStrip (F : OpenPartialHomeomorph (Real × Real) S2) :
    OpenPartialHomeomorph (Real × Real) S2 :=
  stripReflection.toHomeomorph.toOpenPartialHomeomorph.trans F

@[simp] theorem reflectedChart_apply (e : OpenPartialHomeomorph E2 S2) (x : E2) :
    reflectedChart e x = e (saddleCoordinateSwap x) := rfl

@[simp] theorem reflectedStrip_apply (F : OpenPartialHomeomorph (Real × Real) S2)
    (s t : Real) : reflectedStrip F (s, t) = F (s, -t) := rfl

@[simp] theorem mem_reflectedChart_source (e : OpenPartialHomeomorph E2 S2) (x : E2) :
    x ∈ (reflectedChart e).source ↔ saddleCoordinateSwap x ∈ e.source := by
  change (x ∈ (univ : Set E2) ∧ saddleCoordinateSwap x ∈ e.source) ↔ _
  simp

@[simp] theorem mem_reflectedStrip_source (F : OpenPartialHomeomorph (Real × Real) S2)
    (s t : Real) : (s, t) ∈ (reflectedStrip F).source ↔ (s, -t) ∈ F.source := by
  change ((s,t) ∈ (univ : Set (Real × Real)) ∧ (s,-t) ∈ F.source) ↔ _
  simp

theorem reflectedChart_smooth (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (reflectedChart e) (reflectedChart e).source :=
  he.comp coordinateSwap.toContinuousLinearEquiv.toDiffeomorph.contMDiff.contMDiffOn
    (fun x hx => (mem_reflectedChart_source e x).mp hx)

theorem reflectedChart_symm_smooth (e : OpenPartialHomeomorph E2 S2)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (reflectedChart e).symm (reflectedChart e).target :=
  coordinateSwap.toContinuousLinearEquiv.toDiffeomorph.contMDiff.comp_contMDiffOn
    (hei.mono inter_subset_left)

theorem reflectedStrip_smooth (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source) :
    ContMDiffOn IR2 (𝓡 2) ∞ (reflectedStrip F) (reflectedStrip F).source :=
  hF.comp stripReflection.contMDiff.contMDiffOn (by
    rintro ⟨s,t⟩ hx
    exact (mem_reflectedStrip_source F s t).mp hx)

theorem reflectedStrip_symm_smooth (F : OpenPartialHomeomorph (Real × Real) S2)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target) :
    ContMDiffOn (𝓡 2) IR2 ∞ (reflectedStrip F).symm (reflectedStrip F).target :=
  stripReflection.symm.contMDiff.comp_contMDiffOn (hFi.mono inter_subset_left)

theorem reflectedChart_square_source (e : OpenPartialHomeomorph E2 S2) {r : Real}
    (hrs : closedSquare r ⊆ e.source) : closedSquare r ⊆ (reflectedChart e).source := by
  intro x hx
  exact (mem_reflectedChart_source e x).mpr
    (hrs ((saddleCoordinateSwap_mem_closedSquare r x).mpr hx))

theorem reflectedChart_height {v : E3} {g : S2 → E3}
    (e : OpenPartialHomeomorph E2 S2) {c : Real}
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - (x 0)^2 + (x 1)^2) :
    ∀ x ∈ (reflectedChart e).source,
      inner Real (-v) (g (reflectedChart e x)) = -c - (x 0)^2 + (x 1)^2 := by
  intro x hx
  rw [reflectedChart_apply, inner_neg_left, hform _ ((mem_reflectedChart_source e x).mp hx)]
  simp only [saddleCoordinateSwap_zero, saddleCoordinateSwap_one]
  ring

theorem reflectedStrip_height {v : E3} {g : S2 → E3}
    (F : OpenPartialHomeomorph (Real × Real) S2) {c : Real}
    (hheight : ∀ z ∈ F.source, inner Real v (g (F z)) = c + z.2) :
    ∀ z ∈ (reflectedStrip F).source,
      inner Real (-v) (g (reflectedStrip F z)) = -c + z.2 := by
  rintro ⟨s,t⟩ hz
  rw [reflectedStrip_apply, inner_neg_left, hheight _ ((mem_reflectedStrip_source F s t).mp hz)]
  ring

private theorem orthogonal_neg (v : E3) : (Real ∙ v)ᗮ = (Real ∙ (-v))ᗮ := by
  ext x
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right, inner_neg_left]
  exact (neg_eq_zero).symm



def reflectedPlaneFrame {v : E3} (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) :
    E2 ≃ₗᵢ[Real] (Real ∙ (-v))ᗮ :=
  (coordinateSwap.trans J).trans (LinearIsometryEquiv.ofEq _ _ (orthogonal_neg v))

@[simp] theorem reflectedPlaneFrame_coe {v : E3}
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (x : E2) :
    (reflectedPlaneFrame J x : E3) = (J (saddleCoordinateSwap x) : E3) := rfl

theorem reflectedChart_graph {v : E3} {g : S2 → E3}
    (e : OpenPartialHomeomorph E2 S2) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) {c : Real}
    (hgraph : ∀ x ∈ e.source,
      D (g (e x)) = (J x : E3) + (c - (x 0)^2 + (x 1)^2) • v) :
    ∀ x ∈ (reflectedChart e).source,
      D (g (reflectedChart e x)) = (reflectedPlaneFrame J x : E3) +
        (-c - (x 0)^2 + (x 1)^2) • (-v) := by
  intro x hx
  rw [reflectedChart_apply, hgraph _ ((mem_reflectedChart_source e x).mp hx),
    reflectedPlaneFrame_coe]
  simp only [saddleCoordinateSwap_zero, saddleCoordinateSwap_one, smul_neg, ← neg_smul]
  congr 2
  ring

@[simp] theorem negativePatchArc_reflectedChart (e : OpenPartialHomeomorph E2 S2)
    (r t : Real) (i : Fin 2) :
    negativePatchArc (reflectedChart e) r t i = positivePatchArc e r t i := by
  simp only [negativePatchArc, positivePatchArc, image_image]
  congr 1

@[simp] theorem reflectedStrip_negative_slice
    (F : OpenPartialHomeomorph (Real × Real) S2) (a b t : Real) :
    reflectedStrip F '' (Icc a b ×ˢ ({-t} : Set Real)) =
      F '' (Icc a b ×ˢ ({t} : Set Real)) := by
  ext q
  constructor
  · rintro ⟨⟨s,u⟩, ⟨hs, hu⟩, hq⟩
    have he : u = -t := hu
    subst u
    exact ⟨(s,t), ⟨hs, rfl⟩, by simpa only [reflectedStrip_apply, neg_neg] using hq⟩
  · rintro ⟨⟨s,u⟩, ⟨hs, hu⟩, hq⟩
    have he : u = t := hu
    subst u
    exact ⟨(s,-t), ⟨hs, rfl⟩, by simpa only [reflectedStrip_apply, neg_neg] using hq⟩

@[simp] theorem reflectedChart_zero (e : OpenPartialHomeomorph E2 S2) :
    reflectedChart e 0 = e 0 := by
  rw [reflectedChart_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem reflectedChart_contact (e : OpenPartialHomeomorph E2 S2)
    (r : Real) (i : Fin 2 × Fin 2) :
    reflectedChart e (contact r i) = e (contact r (i.2, i.1)) := by
  rw [reflectedChart_apply]
  congr 1

@[simp] theorem reflectedChart_image_openSquare (e : OpenPartialHomeomorph E2 S2)
    (r : Real) : reflectedChart e '' openSquare r = e '' openSquare r := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨saddleCoordinateSwap x, (saddleCoordinateSwap_mem_openSquare r x).mpr hx, rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨saddleCoordinateSwap x, (saddleCoordinateSwap_mem_openSquare r x).mpr hx, ?_⟩
    simp only [reflectedChart_apply, saddleCoordinateSwap_swap]



theorem first_pairing_reflected_of_second_pairing
    (e : OpenPartialHomeomorph E2 S2) (h : S2 → Real) (c r : Real)
    (hsecond : ∀ i j : Fin 2 × Fin 2,
      e (contact r i) ∈ connectedComponentIn
        ({q | h q = c} \ e '' openSquare r) (e (contact r j)) ↔ i.2 = j.2) :
    ∀ i j : Fin 2 × Fin 2,
      reflectedChart e (contact r i) ∈ connectedComponentIn
        ({q | -h q = -c} \ reflectedChart e '' openSquare r)
        (reflectedChart e (contact r j)) ↔ i.1 = j.1 := by
  intro i j
  simpa only [reflectedChart_contact, reflectedChart_image_openSquare, neg_inj]
    using hsecond (i.2,i.1) (j.2,j.1)

theorem reflectedStrip_central_source (F : OpenPartialHomeomorph (Real × Real) S2)
    {a b : Real} (hsource : ∀ s ∈ Icc a b, (s,0) ∈ F.source) :
    ∀ s ∈ Icc a b, (s,0) ∈ (reflectedStrip F).source := by
  intro s hs
  simpa only [mem_reflectedStrip_source, neg_zero] using hsource s hs

theorem reflected_critical_point_avoids_strip (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2) {a b : Real}
    (hnot : e 0 ∉ F '' (Icc a b ×ˢ ({0} : Set Real))) :
    reflectedChart e 0 ∉ reflectedStrip F '' (Icc a b ×ˢ ({0} : Set Real)) := by
  have hslice := reflectedStrip_negative_slice F a b 0
  simp only [neg_zero] at hslice
  simpa only [reflectedChart_zero, hslice] using hnot



theorem positive_anchor_as_reflected_negative
    {v : E3} {g : S2 → E3} (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2) (α : sphere (0 : E2) 1 → S2)
    {c r t a b : Real}
    (hheight : ∀ q, inner Real v (g (α q)) = c + t)
    (hrange : range α ⊆ positivePatchArc e r t 1 ∪ F '' (Icc a b ×ˢ ({t} : Set Real))) :
    (∀ q, inner Real (-v) (g (α q)) = -c - t) ∧
      range α ⊆ negativePatchArc (reflectedChart e) r t 1 ∪
        reflectedStrip F '' (Icc a b ×ˢ ({-t} : Set Real)) := by
  constructor
  · intro q
    rw [inner_neg_left, hheight q]
    ring
  · simpa only [negativePatchArc_reflectedChart, reflectedStrip_negative_slice] using hrange

end Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation
