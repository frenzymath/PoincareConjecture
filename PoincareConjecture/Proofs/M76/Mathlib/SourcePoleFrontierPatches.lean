import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralFrontierDiskPatches
import PoincareConjecture.Proofs.M76.Mathlib.LinearFrontierGermTarget
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace CoordinateHalfBoxes




noncomputable def radialLastToCut (σ : ℝ) (hσ : σ ≠ 0) :
    ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
  (((LinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr (LinearEquiv.prodComm ℝ ℝ ℝ)).trans
      (LinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm)).trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr
      (LinearEquiv.smulOfNeZero ℝ ℝ σ hσ)).prodCongr
        (LinearEquiv.refl ℝ ℝ))).toContinuousLinearEquiv




theorem radialLastToCut_apply (σ : ℝ) (hσ : σ ≠ 0) (x : (ℝ × ℝ) × ℝ) :
    radialLastToCut σ hσ x = ((x.1.1, σ * x.2), x.1.2) := rfl

end CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]








theorem exists_source_pole_frontier_patch
    {C S : Set E} (H : Finset (E →ₗ[ℝ] ℝ))
    (hC : C = {x | ∀ A ∈ H, A x ≤ 1})
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) (A : E →ₗ[ℝ] ℝ)
    (hheight : ∀ x : E, (e x).1.1 = A x)
    {p : E} (hp : p ∈ frontier C) {σ : ℝ} (hσ : σ ≠ 0)
    (hep : e p = ((0, σ), 0))
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    (hS : ∀ x ∈ U, x ∈ S ↔ (e x).2 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : (ℝ × ℝ) → ℝ) (ψ : (ℝ × ℝ) → E) (V : Set E) (r : ℝ),
      Continuous f ∧ f 0 = 1 ∧ Continuous ψ ∧ Function.Injective ψ ∧
      ψ 0 = p ∧ IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ r ∈ Ioo 0 ε ∧
      FinitePiecewiseAffineOn ψ (base r) ∧ ψ '' base r ⊆ frontier C ∩ V ∧
      (∀ x, e (ψ x) = ((x.1, σ * f x), x.2)) ∧
      (∀ x, A (ψ x) = x.1) ∧
      (∀ x ∈ base r, ψ x ∈ S ↔ x.2 = 0) ∧
      IsFinitePLBallPair (ℝ × ℝ) (ψ '' base r) (ψ '' baseBoundary r) ∧
      (∀ T ⊆ base r,
        (frontier C ∩ V) ∩ (fun x => ((e x).1.1, (e x).2)) ⁻¹' T = ψ '' T) ∧
      ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ frontier C ∩ O ⊆ ψ '' base r := by
  classical
  let L := (radialLastToCut σ hσ).trans e.symm
  have hLcoords (q : (ℝ × ℝ) × ℝ) : e (L q) = ((q.1.1, σ * q.2), q.1.2) := by
    change e (e.symm (radialLastToCut σ hσ q)) = _
    rw [e.apply_symm_apply, radialLastToCut_apply]
  have hLpole : L ((0 : ℝ × ℝ), (1 : ℝ)) = p := by
    apply e.injective
    rw [hLcoords, hep]
    change ((0, σ * 1), 0) = ((0, σ), 0)
    rw [mul_one]
  have hprojection (q : (ℝ × ℝ) × ℝ) :
      ((e (L q)).1.1, (e (L q)).2) = q.1 := by
    rw [hLcoords]
  let G := H.image fun B => B.comp L.toLinearMap
  have hbody : L ⁻¹' C = {q | ∀ B ∈ G, B q ≤ 1} := by
    ext q
    rw [hC]
    change (∀ B ∈ H, B (L q) ≤ 1) ↔ ∀ B ∈ G, B q ≤ 1
    constructor
    · intro h B hB
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB
      exact h D hD
    · intro h B hB
      exact h (B.comp L.toLinearMap) (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
  have hfrontpre : frontier {q | ∀ B ∈ G, B q ≤ 1} = L ⁻¹' frontier C := by
    rw [← hbody]
    exact (L.toHomeomorph.preimage_frontier C).symm
  have hpG : ((0 : ℝ × ℝ), (1 : ℝ)) ∈ frontier {q | ∀ B ∈ G, B q ≤ 1} := by
    rw [hfrontpre]
    change L ((0 : ℝ × ℝ), (1 : ℝ)) ∈ frontier C
    rw [hLpole]
    exact hp
  have hG := linear_halfspace_bounds_and_active_of_mem_frontier G hpG
  have hpLU : ((0 : ℝ × ℝ), (1 : ℝ)) ∈ L ⁻¹' U := by
    change L ((0 : ℝ × ℝ), (1 : ℝ)) ∈ U
    rw [hLpole]
    exact hpU
  obtain ⟨f, V₀, r, hf, hf0, hV₀, hpV₀, hV₀U, hr, hfPL, hgraphV₀, _,
    hactual, ⟨O₀, hO₀, hpO₀, hOfront⟩, _⟩ :=
    exists_halfspace_frontier_disk_patch G hG.1 hG.2
      (hU.preimage L.continuous) hpLU hε
  let ψ : (ℝ × ℝ) → E := fun x => L (x, f x)
  let V := L '' V₀
  have hψcoords (x : ℝ × ℝ) : e (ψ x) = ((x.1, σ * f x), x.2) :=
    hLcoords (x, f x)
  have hψprojection (x : ℝ × ℝ) : ((e (ψ x)).1.1, (e (ψ x)).2) = x :=
    hprojection (x, f x)
  have hψi : Function.Injective ψ := by
    intro x y hxy
    exact (hψprojection x).symm.trans
      ((congrArg (fun z : E => ((e z).1.1, (e z).2)) hxy).trans (hψprojection y))
  have hψ0 : ψ 0 = p := by
    change L (0, f 0) = p
    rw [hf0, hLpole]
  have hV : IsOpen V := L.toHomeomorph.isOpenMap V₀ hV₀
  have hpV : p ∈ V := ⟨((0 : ℝ × ℝ), (1 : ℝ)), hpV₀, hLpole⟩
  have hVU : V ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact hV₀U hq
  have hψPL : FinitePiecewiseAffineOn ψ (base r) :=
    hfPL.graph.postcomp L.toContinuousLinearMap.toContinuousAffineMap
  have hψbase : ψ '' base r ⊆ frontier C ∩ V := by
    rintro _ ⟨x, hx, rfl⟩
    have hxgraph : (x, f x) ∈ (fun y => (y, f y)) '' base r := ⟨x, hx, rfl⟩
    have hxfront := (hactual (base r) Subset.rfl).symm.subset hxgraph
    exact ⟨hfrontpre.subset hxfront.1.1, ⟨(x, f x), hgraphV₀ hxgraph, rfl⟩⟩
  refine ⟨f, ψ, V, r, hf, hf0, L.continuous.comp (continuous_id.prodMk hf),
    hψi, hψ0, hV, hpV, hVU, hr, hψPL, hψbase, hψcoords, ?_, ?_,
    (base_ballPair hr.1).image hψPL hψi.injOn, ?_, ?_⟩
  · intro x
    exact (hheight (ψ x)).symm.trans
      (congrArg (fun q : (ℝ × ℝ) × ℝ => q.1.1) (hψcoords x))
  · intro x hx
    have hxU := hVU (hψbase ⟨x, hx, rfl⟩).2
    rw [hS (ψ x) hxU, hψcoords]
  · intro T hT
    apply Subset.antisymm
    · rintro x ⟨⟨hxC, ⟨q, hqV, rfl⟩⟩, hxT⟩
      have hqF := hfrontpre.symm.subset hxC
      have hqT : q.1 ∈ T := by
        change ((e (L q)).1.1, (e (L q)).2) ∈ T at hxT
        rwa [hprojection] at hxT
      obtain ⟨y, hy, hyq⟩ := (hactual T hT).subset ⟨⟨hqF, hqV⟩, hqT⟩
      exact ⟨y, hy, congrArg L hyq⟩
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨hψbase ⟨x, hT hx, rfl⟩, ?_⟩
      change ((e (ψ x)).1.1, (e (ψ x)).2) ∈ T
      rwa [hψprojection]
  · refine ⟨L '' O₀, L.toHomeomorph.isOpenMap O₀ hO₀,
      ⟨((0 : ℝ × ℝ), (1 : ℝ)), hpO₀, hLpole⟩, ?_⟩
    rintro x ⟨hxC, ⟨q, hqO, rfl⟩⟩
    obtain ⟨y, hy, hyq⟩ := hOfront ⟨hfrontpre.symm.subset hxC, hqO⟩
    exact ⟨y, hy, congrArg L hyq⟩

end Geometry.SimplicialComplex
