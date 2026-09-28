import PoincareConjecture.Proofs.M76.Mathlib.SourcePoleQuadrantPatches
import PoincareConjecture.Proofs.M76.Mathlib.LinearPatchConeChart
import PoincareConjecture.Proofs.M76.Mathlib.SignedQuadrantPatchRetention
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes RectangleCornerArcs

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_height_plane_cone_chart_with_cut_boxes
    {S P surface : Set E} {D : Set ((ℝ × ℝ) × ℝ)}
    {H : frontier S ≃ₜ frontier D} (hH : H.IsFinitePL)
    (hS : IsCompact S) (hScv : Convex ℝ S) (hSzero : (0 : E) ∈ interior S)
    (hDcv : Convex ℝ D) (hDzero : (0 : (ℝ × ℝ) × ℝ) ∈ interior D)
    (hdim : Module.finrank ℝ E = 3) (A : E →ₗ[ℝ] ℝ)
    (hpos : ∀ x : frontier S, 0 ≤ A x ↔ 0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1)
    (hneg : ∀ x : frontier S, A x ≤ 0 ↔ (H x : (ℝ × ℝ) × ℝ).1.1 ≤ 0)
    (hPS : P ⊆ frontier S) (hPne : P.Nonempty)
    (hplane : ∀ x : frontier S, (x : E) ∈ P ↔ (H x : (ℝ × ℝ) × ℝ).2 = 0)
    (ψ : Bool → (ℝ × ℝ) → E) (r : Bool → ℝ) (hr : ∀ j, 0 < r j)
    (p : Bool → E) (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hquad : ∀ (j : Bool) (i : Bool × Bool),
      SourcePoleQuadrantData (ψ j) (frontier S) surface
        (frontier S ∩ (surface ∪ {x | A x = 0})) (p j) (p (!j)) A
        (if i.1 then -r j else r j) (if i.2 then -r j else r j))
    (hHL : ∀ (j : Bool) (i : Bool × Bool) (x : frontier S),
      (x : E) ∈ ψ j '' signedRectangle (r j) i → (H x : (ℝ × ℝ) × ℝ) = L j x)
    (hLheight : ∀ j x, (L j x).1.1 = A x)
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (a : Bool → E)
    (hfzero : ∀ j, f j 0 = a j) (hp : ∀ j, p j ∈ frontier S)
    (ρ : Bool → ℝ) (hρ : ∀ j, 1 < ρ j) (hpa : ∀ j, p j = ρ j • a j)
    (O : Bool → Set E) (hO : ∀ j, IsOpen (O j)) (hpO : ∀ j, p j ∈ O j)
    (hOP : ∀ j, frontier S ∩ O j ⊆ ψ j '' base (r j))
    (σ : Bool → ℝ) (hlateral : ∀ j t z, L j (f j ((t, 0), z)) = ((t, σ j), z))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (e : S ≃ₜ T.space) (δ : ℝ),
      δ ∈ Ioo 0 ε ∧ T.faces.Finite ∧ e.IsFinitePL ∧
      (0 : (ℝ × ℝ) × ℝ) ∈ interior T.space ∧
      (e ⟨0, interior_subset hSzero⟩ : (ℝ × ℝ) × ℝ) = 0 ∧
      (∀ x : S, (e x : (ℝ × ℝ) × ℝ).1.1 = A x) ∧
      (∀ x : S, (e x : (ℝ × ℝ) × ℝ).2 = 0 ↔ (x : E) ∈ convexJoin ℝ {0} P) ∧
      (∀ (j : Bool) (i : Bool × Bool) (x : S),
        (x : E) ∈ convexJoin ℝ {0} (ψ j '' signedRectangle (r j) i) →
          (e x : (ℝ × ℝ) × ℝ) = L j x) ∧
      (∀ j, f j '' box δ ⊆ interior S) ∧
      (∀ j (x : S), (x : E) ∈ f j '' box δ → (e x : (ℝ × ℝ) × ℝ) = L j x) ∧
      ∀ j t z, t ∈ Icc (-δ) δ → z ∈ Icc (-δ) δ →
        ∃ x : S, (x : E) = f j ((t, 0), z) ∧
          (e x : (ℝ × ℝ) × ℝ) = ((t, σ j), z) := by
  classical
  let B : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let C : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let Q : Bool × (Bool × Bool) → Set E := fun k => ψ k.1 '' signedRectangle (r k.1) k.2
  let q : Bool × (Bool × Bool) → Set E := fun k =>
    (ψ k.1 '' cornerArc 0 (if k.2.1 then -r k.1 else r k.1)
      0 (if k.2.2 then -r k.1 else r k.1)) ∪
    (ψ k.1 '' cornerArc (if k.2.1 then -r k.1 else r k.1) 0
      (if k.2.2 then -r k.1 else r k.1) 0)
  have hQ (k : Bool × (Bool × Bool)) : IsFinitePLBallPair (ℝ × ℝ) (Q k) (q k) :=
    (hquad k.1 k.2).disk
  have hQS (k : Bool × (Bool × Bool)) : Q k ⊆ frontier S :=
    (hquad k.1 k.2).carrier_subset
  have hdimF : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  obtain ⟨T, e, hT, he, hTzero, hezero, heheight, heplane, hkeep⟩ :=
    hH.exists_height_plane_cone_chart_linear_patches hS hScv hSzero hDcv hDzero
      (hdim.trans hdimF.symm) A B C hpos hneg hPS hPne hplane Q q hQ hQS
      (fun k => L k.1) (fun k => hHL k.1 k.2) (fun k x _ => hLheight k.1 x)
  have hlocal := fun j : Bool =>
    (f j).exists_box_eq_linear_of_signed_quadrant_cones hScv hSzero
      (hfzero j) (hp j) (hρ j) (hpa j) (ψ j) (hr j).le
      (hO j) (hpO j) (hOP j) (fun x : S => (e x : (ℝ × ℝ) × ℝ))
      (L j).toLinearMap (fun i => hkeep (j, i))
  choose δ₀ hδ₀ hbox₀ hboxkeep₀ using hlocal
  obtain ⟨δ, hδ, hsmall⟩ :=
    (Set.toFinite (univ : Set Bool)).exists_pos_lt_positive_values δ₀ hε
  have hboxsub (j : Bool) : box δ ⊆ box (δ₀ j) := by
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall (hsmall j (mem_univ j) (hδ₀ j)).le
  have hbox (j : Bool) : f j '' box δ ⊆ interior S :=
    (image_mono (hboxsub j)).trans (hbox₀ j)
  have hboxkeep (j : Bool) (x : S) (hx : (x : E) ∈ f j '' box δ) :
      (e x : (ℝ × ℝ) × ℝ) = L j x :=
    hboxkeep₀ j x (image_mono (hboxsub j) hx)
  refine ⟨T, e, δ, hδ, hT, he, hTzero, hezero, heheight, heplane,
    fun j i => hkeep (j, i), hbox, hboxkeep, ?_⟩
  intro j t z ht hz
  have hxbox : ((t, 0), z) ∈ box δ :=
    ⟨⟨ht, neg_nonpos.mpr hδ.1.le, hδ.1.le⟩, hz⟩
  have hximage : f j ((t, 0), z) ∈ f j '' box δ := ⟨((t, 0), z), hxbox, rfl⟩
  let x : S := ⟨f j ((t, 0), z), interior_subset (hbox j hximage)⟩
  exact ⟨x, rfl, (hboxkeep j x hximage).trans (hlateral j t z)⟩

end Homeomorph
