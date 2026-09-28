import PoincareConjecture.Proofs.M76.Mathlib.CommonRadiusLateralBoxes
import PoincareConjecture.Proofs.M76.Mathlib.CyclicPrismContactConfinement
import PoincareConjecture.Proofs.M76.Mathlib.SameChartPrismRestriction
import PoincareConjecture.Proofs.M76.Mathlib.OriginalCutPrismContact
import PoincareConjecture.Proofs.M76.Mathlib.RetainedCutAxisImage











set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}






theorem exists_actual_common_cut_box_family
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (R : Fin (n + 3) → ℝ) (hR : ∀ i, 0 < R i)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → E)
    (H : Fin (n + 3) → OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
    (σ k : Fin (n + 3) → Bool → ℝ)
    (hσ : ∀ i, σ i false < σ i true) (hk : ∀ i j, 0 < k i j)
    (hform : ∀ i, F i = (H i).symm ∘
      longitudinalPrismCoordinates (R i) (σ i false) (σ i true))
    (hsource : ∀ i, F i '' box (R i) ⊆ (H i).source)
    (hforward : ∀ i x, x ∈ box (R i) →
      H i (F i x) = longitudinalPrismCoordinates (R i) (σ i false) (σ i true) x)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box (R i)))
    (hinjF : ∀ i, InjOn (F i) (box (R i)))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-R i) (R i)) ×ˢ {0}) = P.cutArc t i)
    (A : E → ℝ) (c : ℝ)
    (hheight : ∀ i x, x ∈ box (R i) → A (F i x) = c + x.1.1)
    {S : Set E} (hplane : ∀ i x, x ∈ box (R i) → (F i x ∈ S ↔ x.2 = 0))
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hfzero : ∀ i, f i 0 = P.edgeCut t i)
    (hcutSource : ∀ i (j : Bool),
      f (if j then finRotate (n + 3) i else i) '' box (R i) ⊆ (H i).source)
    (hcutForward : ∀ i (j : Bool) x, x ∈ box (R i) →
      H i (f (if j then finRotate (n + 3) i else i) x) =
        ((x.1.1, σ i j + k i j * x.1.2), x.2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (G : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → E),
      r ∈ Ioo 0 ε ∧ (∀ i, r < R i) ∧
      (∀ i,
        G i = F i ∘ longitudinalPrismCoordinates r (-R i) (R i) ∧
        G i = (H i).symm ∘ longitudinalPrismCoordinates r (σ i false) (σ i true) ∧
        FinitePiecewiseAffineOn (G i) (box r) ∧ InjOn (G i) (box r) ∧
        G i '' box r = F i '' ((Icc (-r) r ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-r) r) ∧
        G i '' box r ⊆ F i '' box (R i) ∧
        IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (G i '' box r) (G i '' boxBoundary r) ∧
        (∀ x ∈ box r, A (G i x) = c + x.1.1) ∧
        (∀ x ∈ box r, G i x ∈ S ↔ x.2 = 0) ∧
        G i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i ∧
        (∀ x ∈ box r, H i (G i x) =
          longitudinalPrismCoordinates r (σ i false) (σ i true) x) ∧
        ∀ (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
          G i ((u, if j then r else -r), z) =
            f (if j then finRotate (n + 3) i else i) ((u, 0), z)) ∧
      (∀ i, (G i '' box r) ∩ (G (finRotate (n + 3) i) '' box r) =
        f (finRotate (n + 3) i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r)) ∧
      ∀ i j, i ≠ j → finRotate (n + 3) i ≠ j → finRotate (n + 3) j ≠ i →
        Disjoint (G i '' box r) (G j '' box r) := by
  classical
  have hlateral (i : Fin (n + 3)) (j : Bool) (u z : ℝ)
      (hu : u ∈ Icc (-R i) (R i)) (hz : z ∈ Icc (-R i) (R i)) :
      F i ((u, if j then R i else -R i), z) =
        f (if j then finRotate (n + 3) i else i) ((u, 0), z) := by
    have hx : ((u, 0), z) ∈ box (R i) :=
      ⟨⟨hu, neg_nonpos.mpr (hR i).le, (hR i).le⟩, hz⟩
    have hxsource := hcutSource i j (mem_image_of_mem _ hx)
    have hxvalue := hcutForward i j ((u, 0), z) hx
    simp only [mul_zero, add_zero] at hxvalue
    rw [hform i, Function.comp_apply]
    cases j
    · change (H i).symm
        (longitudinalPrismCoordinates (R i) (σ i false) (σ i true) ((u, -R i), z)) =
          f i ((u, 0), z)
      rw [(longitudinalPrismCoordinates_properties (hR i) (hσ i)).2.2.1]
      rw [← hxvalue]
      exact (H i).left_inv hxsource
    · change (H i).symm
        (longitudinalPrismCoordinates (R i) (σ i false) (σ i true) ((u, R i), z)) =
          f (finRotate (n + 3) i) ((u, 0), z)
      rw [(longitudinalPrismCoordinates_properties (hR i) (hσ i)).2.2.2]
      rw [← hxvalue]
      exact (H i).left_inv hxsource
  obtain ⟨q, hq, hqbound⟩ :=
    (Set.toFinite (univ : Set (Fin (n + 3)))).exists_pos_lt_positive_values R hε
  have hqR (i : Fin (n + 3)) : q < R i := hqbound i (mem_univ i) (hR i)
  obtain ⟨ρ, hρ, _, _, hcontactControl⟩ :=
    P.exists_thin_original_cutArc_contacts hP hinjP t ht R hR F
      (fun i => (hF i).continuousOn) hcore f hfzero (q := q) (ε := q) hq.1 hq.1
  obtain ⟨r, G, hr, hrR, hfamily⟩ :=
    exists_common_radius_fixed_lateral_boxes R hR F hF hinjF A c hheight hplane
      (fun i j x => f (if j then finRotate (n + 3) i else i) x) hlateral hρ.1
  simp only [forall_and] at hfamily
  rcases hfamily with ⟨hGform, hGPL, hGinj, hGimage, hGsub, hGball, hGheight,
    hGplane, hGlateral⟩
  have hrq : r < q := hr.2.trans hρ.2
  have hrestriction (i : Fin (n + 3)) :=
    (H i).restrict_fixed_lateral_inverse_box hr.1 (hR i) (hrR i).le (hσ i)
      (F i) (hform i) (hsource i) (hforward i)
  have hGsame (i : Fin (n + 3)) :
      G i = (H i).symm ∘ longitudinalPrismCoordinates r (σ i false) (σ i true) := by
    rw [hGform i]
    exact (hrestriction i).1
  have hGinverse (i : Fin (n + 3)) : G i '' box r =
      (H i).symm '' ((Icc (-r) r ×ˢ Icc (σ i false) (σ i true)) ×ˢ Icc (-r) r) := by
    rw [hGform i]
    exact (hrestriction i).2.2.1
  have htarget (i : Fin (n + 3)) :
      (Icc (-r) r ×ˢ Icc (σ i false) (σ i true)) ×ˢ Icc (-r) r ⊆ (H i).target :=
    (hrestriction i).2.2.2.2.1
  have hGforward (i : Fin (n + 3)) : ∀ x ∈ box r,
      H i (G i x) = longitudinalPrismCoordinates r (σ i false) (σ i true) x := by
    rw [hGform i]
    exact (hrestriction i).2.2.2.2.2
  have hGcore (i : Fin (n + 3)) :
      G i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i := by
    rw [hGform i]
    calc
      (F i ∘ longitudinalPrismCoordinates r (-R i) (R i)) ''
          (({0} ×ˢ Icc (-r) r) ×ˢ {0}) =
        F i '' (longitudinalPrismCoordinates r (-R i) (R i) ''
          (({0} ×ˢ Icc (-r) r) ×ˢ {0})) :=
        (image_image (F i) (longitudinalPrismCoordinates r (-R i) (R i))
          (({0} ×ˢ Icc (-r) r) ×ˢ {0})).symm
      _ = F i '' (({0} ×ˢ Icc (-R i) (R i)) ×ˢ {0}) := by
        rw [longitudinalPrismCoordinates_image_axis hr.1 (show -R i < R i by linarith [hR i])]
      _ = _ := hcore i
  have hboxSub (i : Fin (n + 3)) : box q ⊆ box (R i) := by
    have hI : Icc (-q) q ⊆ Icc (-R i) (R i) := by
      intro x hx
      exact ⟨(neg_le_neg (hqR i).le).trans hx.1, hx.2.trans (hqR i).le⟩
    intro x hx
    exact ⟨⟨hI hx.1.1, hI hx.1.2⟩, hI hx.2⟩
  refine ⟨r, G, ⟨hr.1, hrq.trans hq.2⟩, hrR, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hGform i, hGsame i, hGPL i, hGinj i, hGimage i, hGsub i,
      hGball i, hGheight i, hGplane i, hGcore i, hGforward i, hGlateral i⟩
  · intro i
    let j := finRotate (n + 3) i
    have hcut₀ : f j '' box q ⊆ (H i).source := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcutSource i true ⟨x, hboxSub i hx, rfl⟩
    have hcut₁ : f j '' box q ⊆ (H j).source := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcutSource j false ⟨x, hboxSub j hx, rfl⟩
    have hformula₀ : ∀ x ∈ box q,
        H i (f j x) = ((x.1.1, σ i true + k i true * x.1.2), x.2) :=
      fun x hx => hcutForward i true x (hboxSub i hx)
    have hformula₁ : ∀ x ∈ box q,
        H j (f j x) = ((x.1.1, σ j false + k j false * x.1.2), x.2) :=
      fun x hx => hcutForward j false x (hboxSub j hx)
    have hconfined :
        ((H i).symm '' ((Icc (-r) r ×ˢ Icc (σ i false) (σ i true)) ×ˢ Icc (-r) r)) ∩
          ((H j).symm '' ((Icc (-r) r ×ˢ Icc (σ j false) (σ j true)) ×ˢ Icc (-r) r)) ⊆
            f j '' box q := by
      rw [← hGinverse i, ← hGinverse j, hGimage i, hGimage j]
      exact ((hcontactControl r hr.2.le).1 i).trans (image_mono interior_subset)
    have hcontact := (H i).inverse_prisms_inter_eq_original_cut (H j) (f j)
      hr.1 hrq.le (hσ i).le (hσ j).le (hk i true) (hk j false)
      (htarget i) (htarget j) hcut₀ hcut₁ hformula₀ hformula₁ hconfined
    rw [← hGinverse i, ← hGinverse j] at hcontact
    exact hcontact
  · intro i j hij hi hj
    rw [hGimage i, hGimage j]
    exact (hcontactControl r hr.2.le).2 i j hij hi hj

end Polygon
