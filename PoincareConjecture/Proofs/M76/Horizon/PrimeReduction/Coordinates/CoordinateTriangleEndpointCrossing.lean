import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalTriangleEndpointCrossing

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

noncomputable def crossingCoordinateOrder : C3 ≃ᴬ[ℝ] V3 :=
  let L : C3 ≃ₗ[ℝ] V3 :=
    { toFun := fun z => ![z.1.1, z.2, z.1.2]
      invFun := fun x => ((x 0, x 2), x 1)
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; funext i; fin_cases i <;> rfl
      map_smul' := by intro r x; funext i; fin_cases i <;> rfl }
  L.toContinuousLinearEquiv.toContinuousAffineEquiv

@[simp] theorem crossingCoordinateOrder_apply (z : C3) :
    crossingCoordinateOrder z = ![z.1.1, z.2, z.1.2] := rfl

@[simp] theorem crossingCoordinateOrder_symm_apply (x : V3) :
    crossingCoordinateOrder.symm x = ((x 0, x 2), x 1) := rfl

private theorem exists_local_compatible_endpoint_coordinates
    {X : Type*} [TopologicalSpace X]
    (I B Q : OpenPartialHomeomorph X V3)
    (hB : I.symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hQ : I.symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {y : X} (hyI : y ∈ I.source) (hyB : y ∈ B.source) (hyQ : y ∈ Q.source)
    (T : C3 ≃ᴬ[ℝ] V3) (hT : T 0 = B y)
    {V : Set V3} (hV : IsOpen V) (hyV : B y ∈ V)
    {O : Set V3} (hO : IsOpen O) (hyO : Q y ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 V3,
      H ∈ piecewiseAffineGroupoid V3 ∧ Q y ∈ H.source ∧ H.source ⊆ O ∩ Q.target ∧
      H (Q y) = 0 ∧
      ∀ x ∈ H.source, Q.symm x ∈ B.source ∧ B (Q.symm x) ∈ V ∧
        H x = ![(T.symm (B (Q.symm x))).1.1,
          (T.symm (B (Q.symm x))).2, (T.symm (B (Q.symm x))).1.2] := by
  let C := (I.symm.trans Q).symm.trans (I.symm.trans B)
  have hC : C ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm hQ) hB
  have hyC : Q y ∈ C.source := by
    change (Q y ∈ Q.target ∧ Q.symm (Q y) ∈ I.source) ∧
      (I (Q.symm (Q y)) ∈ I.target ∧ I.symm (I (Q.symm (Q y))) ∈ B.source)
    simpa only [Q.left_inv hyQ, I.left_inv hyI] using
      And.intro (And.intro (Q.map_source hyQ) hyI) (And.intro (I.map_source hyI) hyB)
  have hCy : C (Q y) = B y := by
    change B (I.symm (I (Q.symm (Q y)))) = B y
    rw [Q.left_inv hyQ, I.left_inv hyI]
  have hCval (x : V3) (hx : x ∈ C.source) : C x = B (Q.symm x) := by
    change B (I.symm (I (Q.symm x))) = B (Q.symm x)
    rw [I.left_inv hx.1.2]
  have hback (x : V3) (hx : x ∈ C.source) : Q.symm x ∈ B.source := by
    have hh := hx.2.2
    change I.symm (I (Q.symm x)) ∈ B.source at hh
    rwa [I.left_inv hx.1.2] at hh
  let E := T.symm.trans crossingCoordinateOrder
  have hE : E.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 := by
    exact ⟨locallyPiecewiseAffineOn_affine E.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine E.symm.toContinuousAffineMap isOpen_univ⟩
  let D := C.trans E.toHomeomorph.toOpenPartialHomeomorph
  have hD : D ∈ piecewiseAffineGroupoid V3 := (piecewiseAffineGroupoid V3).trans hC hE
  let U := O ∩ (C.source ∩ C ⁻¹' V)
  have hU : IsOpen U := hO.inter (C.isOpen_inter_preimage hV)
  let H := D.restrOpen U hU
  have hH : H ∈ piecewiseAffineGroupoid V3 :=
    ⟨hD.1.mono H.open_source inter_subset_left,
      hD.2.mono H.open_target inter_subset_left⟩
  have hyH : Q y ∈ H.source :=
    ⟨⟨hyC, mem_univ _⟩, hyO, hyC, by change C (Q y) ∈ V; rw [hCy]; exact hyV⟩
  refine ⟨H, hH, hyH, fun x hx => ⟨hx.2.1, hx.1.1.1.1⟩, ?_, ?_⟩
  · change crossingCoordinateOrder (T.symm (C (Q y))) = 0
    rw [hCy, ← hT, T.symm_apply_apply]
    funext i
    fin_cases i <;> rfl
  · intro x hx
    have hxC : x ∈ C.source := hx.1.1
    refine ⟨hback x hxC, (hCval x hxC) ▸ hx.2.2.2, ?_⟩
    change crossingCoordinateOrder (T.symm (C x)) = _
    rw [hCval x hxC]
    rfl

theorem HasOriginalEdgeCofaceCharts.exists_triangle_endpoint_crossing_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hgi : InjOn g K.space) {y : X} (hyV : y ∉ g '' K.vertices)
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (hycover : ∃ i, y ∈ (e i).source)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hyQ : y ∈ Q.source) {O : Set V3} (hO : IsOpen O) (hyO : Q y ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 V3,
      H ∈ piecewiseAffineGroupoid V3 ∧ Q y ∈ H.source ∧ H.source ⊆ O ∩ Q.target ∧
      H (Q y) = 0 ∧
      (∀ x ∈ H.source, Q.symm x ∈ S ↔ H x 1 = 0) ∧
      (∀ x ∈ H.source,
        Q.symm x ∈ g '' convexHull ℝ ({w, p, q} : Set E) ↔
          H x 0 = 0 ∧ 0 ≤ H x 2) ∧
      (∀ x ∈ H.source, Q.symm x ∈ g '' segment ℝ p q ↔
        H x 0 = 0 ∧ H x 2 = 0) ∧
      ∀ x ∈ H.source,
        Q.symm x ∈ g '' intrinsicFrontier ℝ (convexHull ℝ ({w, p, q} : Set E)) ↔
          H x 0 = 0 ∧ H x 2 = 0 := by
  obtain ⟨B, V, T, hB, hyB, hV, hyV, hVB, hT, hS, htriangle, hedge, hfront⟩ :=
    h.exists_triangle_endpoint_crossing_of_not_vertex hgi hyV hpq hwp hwq ht hy
  obtain ⟨i, hyi⟩ := hycover
  obtain ⟨H, hH, hyH, hHO, hHzero, hvalues⟩ :=
    exists_local_compatible_endpoint_coordinates (e i) B Q (hB i) (hQ i)
      hyi hyB hyQ T hT hV hyV hO hyO
  have hsource (x : V3) (hx : x ∈ H.source) :
      Q.symm x ∈ B.source ∧ T (T.symm (B (Q.symm x))) ∈ V := by
    exact ⟨(hvalues x hx).1, by simpa only [T.apply_symm_apply] using (hvalues x hx).2.1⟩
  have hcoord0 (x : V3) (hx : x ∈ H.source) :
      H x 0 = (T.symm (B (Q.symm x))).1.1 := by rw [(hvalues x hx).2.2]; rfl
  have hcoord1 (x : V3) (hx : x ∈ H.source) :
      H x 1 = (T.symm (B (Q.symm x))).2 := by rw [(hvalues x hx).2.2]; rfl
  have hcoord2 (x : V3) (hx : x ∈ H.source) :
      H x 2 = (T.symm (B (Q.symm x))).1.2 := by rw [(hvalues x hx).2.2]; rfl
  refine ⟨H, hH, hyH, hHO, hHzero, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hh := hS _ (hsource x hx).2
    simpa only [T.apply_symm_apply, B.left_inv (hsource x hx).1, hcoord1 x hx] using hh
  · intro x hx
    have hh := htriangle _ (hsource x hx).2
    simpa only [T.apply_symm_apply, B.left_inv (hsource x hx).1,
      hcoord0 x hx, hcoord2 x hx] using hh
  · intro x hx
    have hh := hedge _ (hsource x hx).2
    simpa only [T.apply_symm_apply, B.left_inv (hsource x hx).1,
      hcoord0 x hx, hcoord2 x hx, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using hh
  · intro x hx
    have hh := hfront _ (hsource x hx).2
    simpa only [T.apply_symm_apply, B.left_inv (hsource x hx).1,
      hcoord0 x hx, hcoord2 x hx, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using hh

end PoincareConjecture.M76
