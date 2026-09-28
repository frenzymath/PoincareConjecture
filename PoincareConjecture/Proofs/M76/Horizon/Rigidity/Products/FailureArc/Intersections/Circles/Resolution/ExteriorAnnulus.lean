import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Cup

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

theorem exists_cup_exterior_annulus
    {X : Type*} [TopologicalSpace X] {A₁ : Set P2} {L d δ : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (hδ : 0 < δ) (hδd : δ < d)
    (B₁ : OrientedPolygonCollar L d A₁) (f₁ : P2 → X)
    (hf : ContinuousOn f₁ (closure B₁.outer.inside))
    (hfi : InjOn f₁ (closure B₁.outer.inside))
    (τ : C3 → X) {A B Cup S : Set X}
    (hA : MapsTo f₁ (closure B₁.outer.inside) A)
    (hB : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ B ↔ z.1.2 = -z.1.1)
    (hcap : Cup ∩ A = f₁ '' closure B₁.inner.inside)
    (hCS : Cup ⊆ S) (hSCB : S ⊆ Cup ∪ B)
    (hperiod : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
      (p : squareAnnulus L d), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), u) →
        f₁ (B₁.chart p) = τ ((u, u), s)) :
    ∃ p : AddCircle (4 * L) × I01 → X,
      Continuous p ∧
      (∀ z, p z ∈ S ↔ (z.2 : ℝ) = 0) ∧
      (range (fun z : AddCircle (4 * L) ↦ p (z, 0))) = f₁ '' B₁.inner.boundary ℝ ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (t : I01),
        p ((s : AddCircle (4 * L)), t) = τ ((d - δ * t, d - δ * t), s)) ∧
      range p ⊆ f₁ '' A₁ := by
  classical
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hdepth (t : I01) : d - δ * (t : ℝ) ∈ Icc (-d) d := by
    constructor <;> nlinarith [t.property.1, t.property.2]
  obtain ⟨E, hE⟩ := exists_annulus_homeomorph hL hd.le hwidth
  let q (z : AddCircle (4 * L) × I01) : squareAnnulus L d :=
    E (z.1, ⟨d - δ * z.2, hdepth z.2⟩)
  have hq : Continuous q := E.continuous.comp (continuous_fst.prodMk
    ((continuous_const.sub (continuous_const.mul (continuous_subtype_val.comp continuous_snd))).subtype_mk _))
  have hqd (z : AddCircle (4 * L) × I01) : depth L (q z : P2) = d - δ * z.2 := by
    rw [show (q z : P2) = annulusMap L hL (z.1, d - δ * z.2) from hE _]
    exact depth_annulusMap hL
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr (hdepth z.2)) (by norm_num)) hwidth) _
  have hsub : A₁ ⊆ closure B₁.outer.inside := B₁.carrier.subset.trans sdiff_subset
  let p (z : AddCircle (4 * L) × I01) := f₁ (B₁.chart (q z))
  have hp : Continuous p := hf.comp_continuous
    (continuous_subtype_val.comp (B₁.chart.continuous.comp hq))
    (fun z ↦ hsub (B₁.chart (q z)).property)
  have hpv (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (t : I01) :
      p ((s : AddCircle (4 * L)), t) = τ ((d - δ * t, d - δ * t), s) :=
    hperiod s hs ⟨d - δ * t, hdepth t⟩ (q ((s : AddCircle (4 * L)), t)) (hE _)
  have hrep (z : AddCircle (4 * L)) :
      ∃ s ∈ Icc 0 (4 * L), (s : AddCircle (4 * L)) = z :=
    ⟨AddCircle.equivIco (4 * L) 0 z,
      ⟨(AddCircle.equivIco (4 * L) 0 z).property.1,
        by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0 z).property.2.le⟩,
      AddCircle.coe_equivIco⟩
  have hpin (z : AddCircle (4 * L) × I01) : p z ∈ A := hA (hsub (B₁.chart (q z)).property)
  have hpB (z : AddCircle (4 * L) × I01) : p z ∉ B := by
    obtain ⟨s, hs, hz⟩ := hrep z.1
    obtain ⟨w, t⟩ := z
    dsimp at hz ⊢
    subst w
    rw [hpv s hs t, hB _ ⟨⟨hdepth t, hdepth t⟩, hs⟩]
    have hv : 0 < d - δ * (t : ℝ) := by nlinarith [t.property.2]
    linarith
  have hpS (z : AddCircle (4 * L) × I01) : p z ∈ S ↔ (z.2 : ℝ) = 0 := by
    constructor
    · intro hz
      have hCup := (hSCB hz).resolve_right (hpB z)
      obtain ⟨x, hx, hxeq⟩ := hcap.subset ⟨hCup, hpin z⟩
      have hxout := B₁.nested.trans subset_closure hx
      have hxeq' := hfi hxout (hsub (B₁.chart (q z)).property) hxeq
      have hin : (B₁.chart (q z) : P2) ∈ closure B₁.inner.inside := hxeq' ▸ hx
      have hbdy : (B₁.chart (q z) : P2) ∈ B₁.inner.boundary ℝ := by
        rw [← B₁.inner.frontier_inside B₁.inner_simplicial B₁.inner_injective, frontier,
          (B₁.inner.isOpen_inside B₁.inner_simplicial B₁.inner_injective).interior_eq]
        exact ⟨hin, (B₁.carrier.subset (B₁.chart (q z)).property).2⟩
      have hdpt := (B₁.inner_depth (q z)).mp hbdy
      rw [hqd] at hdpt
      exact (mul_eq_zero.mp (by linarith : δ * (z.2 : ℝ) = 0)).resolve_left hδ.ne'
    · intro hz
      apply hCS
      apply (hcap.symm.subset ?_).1
      refine ⟨B₁.chart (q z), ?_, rfl⟩
      apply (B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective).1
      apply (B₁.inner_depth _).mpr
      rw [hqd, hz, mul_zero, sub_zero]
  refine ⟨p, hp, hpS, ?_, hpv, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨B₁.chart (q (z, 0)), (B₁.inner_depth _).mpr ?_, rfl⟩
      simpa using hqd (z, 0)
    · rintro ⟨x, hx, rfl⟩
      have hxA := (oriented_collar_boundary_subsets B₁).2 hx
      let v := B₁.chart.symm ⟨x, hxA⟩
      have hcv : (B₁.chart v : P2) = x := congrArg Subtype.val (B₁.chart.apply_symm_apply _)
      have hdv := (B₁.inner_depth v).mp (hcv.symm ▸ hx)
      obtain ⟨s, hs, hv⟩ := exists_period_parameter_of_depth hd hwidth v
      have heq : q ((s : AddCircle (4 * L)), 0) = v := by
        apply Subtype.ext
        rw [show (q ((s : AddCircle (4 * L)), 0) : P2) =
          annulusMap L hL ((s : AddCircle (4 * L)), d - δ * (0 : I01)) from hE _]
        simpa [hdv] using hv.symm
      exact ⟨(s : AddCircle (4 * L)), by change f₁ (B₁.chart (q (_, 0))) = f₁ x; rw [heq, hcv]⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨B₁.chart (q z), (B₁.chart (q z)).property, rfl⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
