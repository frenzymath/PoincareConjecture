import PoincareConjecture.Proofs.M76.Triangulation.ActualInwardFrontierMap
import PoincareConjecture.Proofs.M76.Mathlib.ActualPoleCutConeChart
import PoincareConjecture.Proofs.M76.Mathlib.FixedLateralInverseBox
import PoincareConjecture.Proofs.M76.Mathlib.RetainedCutAxisImage

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_actual_original_cut_box
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ K.faces) (hcard : ∀ j, (s j).card = 3)
    (a p : Bool → E)
    (ha : ∀ j, a j ∈ intrinsicInterior ℝ (convexHull ℝ (s j : Set E)))
    (hp : ∀ j, p j ∈ intrinsicInterior ℝ (convexHull ℝ (s j : Set E)))
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hfzero : ∀ j, f j 0 = a j)
    {R : ℝ} (hR : 0 < R)
    (hsurface : ∀ j x, x ∈ box R → (f j x ∈ K.space ↔ x.2 = 0))
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hflast : ∀ j x, (L j (f j x)).2 = x.2)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hheight : ∀ j x, (L j x).1.1 = A x)
    (hfheight : ∀ j x, A (f j x) = x.1.1)
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (hinward : ∀ j x, x ∈ box R → x.1.1 = 0 → (f j x ∈ d ↔ 0 ≤ x.2))
    (B : SimplicialComplex ℝ E) (hB : B.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hBC : B.space = C) (hzero : (0 : E) ∈ interior C)
    (Z : Finset (E →ₗ[ℝ] ℝ)) (hZ : C = {x | ∀ Q ∈ Z, Q x ≤ 1})
    (hpC : ∀ j, p j ∈ frontier C) (hpne : p false ≠ p true)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hPS : P.boundary ℝ = frontier C ∩ K.space)
    (hPzero : P.boundary ℝ ∩ {x | A x = 0} = {p false, p true})
    (hnegP : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hposP : ∃ x ∈ P.boundary ℝ, 0 < A x)
    (hcone : C ∩ K.space = convexJoin ℝ {0} (P.boundary ℝ))
    (ρ : Bool → ℝ) (hρ : ∀ j, 1 < ρ j) (hpa : ∀ j, p j = ρ j • a j)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true)
    (hlateral : ∀ j t z, L j (f j ((t, 0), z)) = ((t, σ j), z))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
      (F : ((ℝ × ℝ) × ℝ) → E),
      δ ∈ Ioo 0 ε ∧ δ < R ∧ H.source = interior C ∧
      F = H.symm ∘ longitudinalPrismCoordinates δ (σ false) (σ true) ∧
      F '' box δ ⊆ interior C ∧
      FinitePiecewiseAffineOn F (box δ) ∧ InjOn F (box δ) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (F '' box δ) (F '' boxBoundary δ) ∧
      (∀ x ∈ box δ, A (F x) = x.1.1) ∧
      (∀ x ∈ box δ, F x ∈ K.space ↔ x.2 = 0) ∧
      (∀ j t z, t ∈ Icc (-δ) δ → z ∈ Icc (-δ) δ →
        F ((t, if j then δ else -δ), z) = f j ((t, 0), z)) ∧
      (∀ j, f j '' box δ ⊆ H.source) ∧
      (∀ j x, x ∈ box δ → H (f j x) = L j (f j x)) ∧
      (∀ x ∈ box δ,
        H (F x) = longitudinalPrismCoordinates δ (σ false) (σ true) x) ∧
      F '' (({0} ×ˢ Icc (-δ) δ) ×ˢ {0}) =
        segment ℝ 0 (a false) ∪ segment ℝ 0 (a true) := by
  have hLa (j : Bool) : L j (a j) = ((0, σ j), 0) := by
    rw [← hfzero j]
    exact hlateral j 0 0
  let poleScalar (j : Bool) : ℝ := ρ j * σ j
  have hpoleNeg : poleScalar false < 0 :=
    mul_neg_of_pos_of_neg (zero_lt_one.trans (hρ false)) hσneg
  have hpolePos : 0 < poleScalar true :=
    mul_pos (zero_lt_one.trans (hρ true)) hσpos
  have hLp (j : Bool) : L j (p j) = ((0, poleScalar j), 0) := by
    rw [hpa j, map_smul, hLa j]
    simp only [poleScalar, Prod.smul_mk, smul_eq_mul, mul_zero]
  obtain ⟨D, G, ψ, r, O, hD, hDc, hDcv, hDzero, hG, hpatch, hGL,
    hpos, hneg, hplane⟩ :=
    K.exists_actual_inward_frontier_map hK hbound s hs hcard a p ha hp f hfzero
      hR hsurface L hflast A hA hdim hheight hfheight hd hdplane hinward
      B hB hC hcv hBC hzero Z hZ hpC hpne P hP hinjP hPS hPzero hnegP hposP
      poleScalar hpoleNeg hpolePos hLp (fun _ => R) (fun _ => hR)
  simp only [forall_and] at hpatch
  rcases hpatch with ⟨_, _, hψzero, hr, _, _, _, _, _, hO, hpO, hOP, hquad⟩
  have hlinkSub : P.boundary ℝ ⊆ frontier C := by
    rw [hPS]
    exact inter_subset_left
  have hlinkNe : (P.boundary ℝ).Nonempty := ⟨hnegP.choose, hnegP.choose_spec.1⟩
  have hlinkPlane (x : frontier C) :
      (x : E) ∈ P.boundary ℝ ↔ (G x : (ℝ × ℝ) × ℝ).2 = 0 := by
    rw [hPS]
    exact (and_iff_right x.property).trans (hplane x)
  obtain ⟨T, e, η, hη, _, he, _, _, heheight, heplane, hkeep, hbox, hboxkeep, _⟩ :=
    hG.exists_height_plane_cone_chart_with_cut_boxes hC hcv hzero hDcv hDzero
      hdim A hpos hneg hlinkSub hlinkNe hlinkPlane ψ r (fun j => (hr j).1)
      p L hquad (fun j i => hGL i j) hheight f a hfzero hpC ρ hρ hpa
      O hO hpO hOP σ hlateral (lt_min hε hR)
  have heSurface (x : C) :
      (e x : (ℝ × ℝ) × ℝ).2 = 0 ↔ (x : E) ∈ K.space := by
    rw [heplane x, ← hcone]
    exact and_iff_right x.property
  let Q (j : Bool) : Set E := ψ j '' signedRectangle (r j) (false, false)
  have hpQ (j : Bool) : p j ∈ Q j :=
    ⟨0, ⟨left_mem_uIcc, left_mem_uIcc⟩, hψzero j⟩
  have hpIn (j : Bool) : p j ∈ C := hC.isClosed.frontier_subset (hpC j)
  have haxis := he.longitudinal_axis_mem_interior_of_linear_cones hdim hcv hzero
    Q p a hpIn hpQ ρ hρ hpa L (fun j => hkeep j (false, false)) σ hσneg hσpos hLa
  obtain ⟨H, δ, F, hδ, hsource, _, _, hInv, hF, hPT, hFPL, hFinj,
    _, _, hball, hcutSource, hforward, hFheight, hFplane, hFlateral⟩ :=
    he.exists_fixed_lateral_inverse_box hdim A heheight heSurface σ (hσneg.trans hσpos)
      haxis f L hη.1 hbox hboxkeep hlateral
  let N := longitudinalPrismCoordinates δ (σ false) (σ true)
  have hNimage := (longitudinalPrismCoordinates_properties hδ.1 (hσneg.trans hσpos)).2.1
  have hNtarget (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box δ) : N x ∈ H.target :=
    hPT (hNimage.subset (mem_image_of_mem _ hx))
  have hFsource : F '' box δ ⊆ interior C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hF, Function.comp_apply, ← hsource]
    exact H.map_target (hNtarget x hx)
  have hFforward (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box δ) : H (F x) = N x := by
    rw [hF, Function.comp_apply]
    exact H.right_inv (hNtarget x hx)
  have hcore := e.image_axis_inverse_of_linear_cones H.symm hInv hcv
    (interior_subset hzero) Q p a hpIn hpQ ρ hρ hpa L
    (fun j => hkeep j (false, false)) σ hσneg hσpos hLa
  refine ⟨δ, H, F, ⟨hδ.1, hδ.2.trans (hη.2.trans_le (min_le_left _ _))⟩,
    hδ.2.trans (hη.2.trans_le (min_le_right _ _)), hsource, hF, hFsource,
    hFPL, hFinj, hball, hFheight, hFplane, hFlateral, hcutSource, hforward,
    hFforward, ?_⟩
  calc
    F '' (({0} ×ˢ Icc (-δ) δ) ×ˢ {0}) =
        H.symm '' (N '' (({0} ×ˢ Icc (-δ) δ) ×ˢ {0})) := by
      rw [hF]
      exact (image_image H.symm N _).symm
    _ = H.symm '' (({0} ×ˢ Icc (σ false) (σ true)) ×ˢ {0}) := by
      rw [longitudinalPrismCoordinates_image_axis hδ.1 (hσneg.trans hσpos)]
    _ = _ := hcore

end Geometry.SimplicialComplex
