import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PrescribedModelChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedModelNesting








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel
open Plane.Isotopy.ArcPairs

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem lift_projection {y : E3} {z : Real} (hy : y 2 = z) :
    Saddle.toE3 (Saddle.toE2 y) z = y := by
  ext i
  fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hy]

private theorem projection_lift (x : E2) (z : Real) :
    Saddle.toE2 (Saddle.toE3 x z) = x := by
  ext i
  fin_cases i <;> rfl

private theorem smooth_projection : ContDiff Real ∞ Saddle.toE2 := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff

private theorem smooth_lift (z : Real) : ContDiff Real ∞ (fun x : E2 => Saddle.toE3 x z) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  · exact contDiff_const

private def heightFiber (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hG : ∀ y, G y 2 = y 2) (z : Real) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := Saddle.toE2 (G (Saddle.toE3 x z))
  invFun x := Saddle.toE2 (G.symm (Saddle.toE3 x z))
  left_inv x := by
    change Saddle.toE2 (G.symm (Saddle.toE3 (Saddle.toE2 (G (Saddle.toE3 x z))) z)) = x
    have hg : G (Saddle.toE3 x z) 2 = z := hG _
    rw [lift_projection hg, G.symm_apply_apply, projection_lift]
  right_inv x := by
    change Saddle.toE2 (G (Saddle.toE3 (Saddle.toE2 (G.symm (Saddle.toE3 x z))) z)) = x
    have hGi : G.symm (Saddle.toE3 x z) 2 = z := by
      have hh := (hG (G.symm (Saddle.toE3 x z))).symm
      rw [G.apply_symm_apply] at hh
      exact hh
    rw [lift_projection hGi, G.apply_symm_apply, projection_lift]
  contMDiff_toFun := (smooth_projection.comp (G.contDiff.comp (smooth_lift z))).contMDiff
  contMDiff_invFun := (smooth_projection.comp (G.symm.contDiff.comp (smooth_lift z))).contMDiff

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem flatten_height (d : TerminalSaddleGeometry M P p e) (y : E3) :
    d.flatten y 2 = inner Real (M.v : E3) y :=
  (d.frame_height (d.D y)).trans (d.D_height y)

private def modelTransition (d₁ d₂ : TerminalSaddleGeometry M P p e) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  (d₁.transport.trans d₁.flatten).symm.trans (d₂.transport.trans d₂.flatten)

private theorem modelTransition_height
    (d₁ d₂ : TerminalSaddleGeometry M P p e)
    (hmodel : d₂.model = d₁.model) (hscale : d₂.scale = d₁.scale)
    (hchart : d₂.modelChart = negativeBranchReflectedChart d₁.modelChart) :
    ∀ y, modelTransition d₁ d₂ y 2 = y 2 := by
  have hcenter : d₂.model (d₂.modelChart 0) = d₁.model (d₁.modelChart 0) := by
    rw [hmodel, hchart, negativeBranchReflectedChart_zero]
  intro y
  let H₁ := d₁.transport.trans d₁.flatten
  have hh := flatten_height d₁ (d₁.transport (H₁.symm y))
  rw [d₁.transport_height] at hh
  change H₁ (H₁.symm y) 2 = _ at hh
  rw [H₁.apply_symm_apply] at hh
  change d₂.flatten (d₂.transport (H₁.symm y)) 2 = y 2
  rw [flatten_height, d₂.transport_height, hscale, hcenter]
  exact hh.symm

private theorem modelTransition_model_image
    (d₁ d₂ : TerminalSaddleGeometry M P p e) (hmodel : d₂.model = d₁.model) :
    modelTransition d₁ d₂ '' (d₁.flatten '' (d₁.filledModel '' sphere (0 : E3) 1)) =
      d₂.flatten '' (d₂.filledModel '' sphere (0 : E3) 1) := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨d₂.filledModel x, ⟨x, hx, rfl⟩, ?_⟩
    change d₂.flatten (d₂.transport (d₂.model x)) =
      (d₂.transport.trans d₂.flatten)
        ((d₁.transport.trans d₁.flatten).symm ((d₁.transport.trans d₁.flatten) (d₁.model x)))
    rw [Diffeomorph.symm_apply_apply, hmodel]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨d₁.flatten (d₁.filledModel x), ⟨d₁.filledModel x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    change (d₂.transport.trans d₂.flatten)
        ((d₁.transport.trans d₁.flatten).symm ((d₁.transport.trans d₁.flatten) (d₁.model x))) =
      d₂.flatten (d₂.transport (d₂.model x))
    rw [Diffeomorph.symm_apply_apply, hmodel]
    rfl

private theorem heightFiber_image_fiber
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (hG : ∀ y, G y 2 = y 2)
    (z : Real) (A B : Set E3) (hAB : G '' A = B) :
    heightFiber G hG z '' {x | Saddle.toE3 x z ∈ A} = {x | Saddle.toE3 x z ∈ B} := by
  have hlift (x : E2) : Saddle.toE3 (heightFiber G hG z x) z = G (Saddle.toE3 x z) :=
    lift_projection (hG (Saddle.toE3 x z))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change Saddle.toE3 (heightFiber G hG z y) z ∈ B
    rw [hlift, ← hAB]
    exact mem_image_of_mem G hy
  · intro hx
    refine ⟨(heightFiber G hG z).symm x, ?_, (heightFiber G hG z).apply_symm_apply x⟩
    have hi := hlift ((heightFiber G hG z).symm x)
    rw [(heightFiber G hG z).apply_symm_apply] at hi
    change Saddle.toE3 ((heightFiber G hG z).symm x) z ∈ A
    have hm : G (Saddle.toE3 ((heightFiber G hG z).symm x) z) ∈ G '' A := by
      rw [hAB, ← hi]
      exact hx
    obtain ⟨y, hy, heq⟩ := hm
    exact G.injective heq ▸ hy

private theorem modelTransition_patch
    (d₁ d₂ : TerminalSaddleGeometry M P p e)
    (hmodel : d₂.model = d₁.model) (hscale : d₂.scale = d₁.scale)
    (hchart : d₂.modelChart = negativeBranchReflectedChart d₁.modelChart)
    {y : E2} (hy₁ : y ∈ closedBall 0 d₁.matchingRadius)
    (hy₂ : negativeBranchReflection y ∈ closedBall 0 d₂.matchingRadius) :
    modelTransition d₁ d₂ (d₁.flatten (g (e (Real.sqrt d₁.scale • y)))) =
      d₂.flatten (g (e (negativeBranchReflection (Real.sqrt d₁.scale • y)))) := by
  have hinvol : negativeBranchReflection (negativeBranchReflection y) = y := by
    ext i
    fin_cases i <;> simp
  have hm₂ := d₂.matching (negativeBranchReflection y) hy₂
  rw [hmodel, hchart, negativeBranchReflectedChart_apply, hinvol, hscale,
    ← map_smul] at hm₂
  rw [← d₁.matching y hy₁]
  change (d₂.transport.trans d₂.flatten)
      ((d₁.transport.trans d₁.flatten).symm
        ((d₁.transport.trans d₁.flatten) (d₁.model (d₁.modelChart y)))) = _
  rw [Diffeomorph.symm_apply_apply]
  exact congrArg d₂.flatten hm₂



theorem exists_reflected_nested_model_planar_transition
    (d₁ d₂ : TerminalSaddleGeometry M P p e)
    (hmodel₁ : d₁.model = Saddle.Nested.shear (3 / 10))
    (hmodel₂ : d₂.model = Saddle.Nested.shear (3 / 10))
    (hscale : d₂.scale = d₁.scale)
    (hchart : d₂.modelChart = negativeBranchReflectedChart d₁.modelChart)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - (x 0)^2 + (x 1)^2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        R '' d₁.B (inner Real (M.v : E3) (g p) - t) =
          d₂.B (inner Real (M.v : E3) (g p) - t) ∧
        ∀ i, R (Saddle.toE2 (d₁.flatten (g (e (negativeLevelArc t i 0))))) =
          Saddle.toE2 (d₂.flatten (g (e
            (negativeLevelArc t (Equiv.swap (0 : Fin 2) 1 i) 0)))) := by
  let m := min d₁.matchingRadius d₂.matchingRadius
  have hm : 0 < m := lt_min d₁.matchingRadius_pos d₂.matchingRadius_pos
  have hroot : 0 < Real.sqrt d₁.scale := Real.sqrt_pos.mpr d₁.scale_pos
  have hmodel : d₂.model = d₁.model := hmodel₂.trans hmodel₁.symm
  have hG := modelTransition_height d₁ d₂ hmodel hscale hchart
  refine ⟨(Real.sqrt d₁.scale * m)^2, sq_pos_of_pos (mul_pos hroot hm), ?_⟩
  intro t ht
  let z := inner Real (M.v : E3) (g p) - t
  let R := heightFiber (modelTransition d₁ d₂) hG z
  refine ⟨R, heightFiber_image_fiber _ hG z _ _
    (modelTransition_model_image d₁ d₂ hmodel), ?_⟩
  intro i
  let x := negativeLevelArc t i 0
  let y := (Real.sqrt d₁.scale)⁻¹ • x
  have hnormsq : ‖x‖^2 = t := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> simp [x, negativeLevelArc, positiveLevelArc, saddleCoordinateSwap,
      Fin.sum_univ_two, Real.sq_sqrt ht.1.le]
  have hxnorm : ‖x‖ ≤ Real.sqrt d₁.scale * m := by
    nlinarith [ht.2, norm_nonneg x, mul_pos hroot hm]
  have hynorm : ‖y‖ ≤ m := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot), inv_mul_eq_div]
    exact (div_le_iff₀ hroot).mpr (by nlinarith [hxnorm])
  have hy₁ : y ∈ closedBall 0 d₁.matchingRadius :=
    mem_closedBall_zero_iff.mpr (hynorm.trans (min_le_left _ _))
  have hy₂ : negativeBranchReflection y ∈ closedBall 0 d₂.matchingRadius := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact hynorm.trans (min_le_right _ _)
  have hcancel : Real.sqrt d₁.scale • y = x := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hroot.ne', one_smul]
  have hxsource : x ∈ e.source := hcancel ▸ d₁.matching_actual_source y hy₁
  have hheight : d₁.flatten (g (e x)) 2 = z := by
    rw [flatten_height, hform x hxsource]
    have hxlevel := negativeLevelArc_height ht.1 i 0
    change -(x 0)^2 + (x 1)^2 = -t at hxlevel
    dsimp [z]
    linarith
  have hpatch := modelTransition_patch d₁ d₂ hmodel hscale hchart hy₁ hy₂
  rw [hcancel, negativeBranchReflection_negativeLevelArc] at hpatch
  change Saddle.toE2 (modelTransition d₁ d₂
    (Saddle.toE3 (Saddle.toE2 (d₁.flatten (g (e x)))) z)) = _
  rw [lift_projection hheight, hpatch]

private theorem circle_pair_disjoint_of_joint_injective
    (C : Fin 2 → S1 → E2) (hi : Injective (fun x : Fin 2 × S1 => C x.1 x.2)) :
    Disjoint (range (C 0)) (range (C 1)) := by
  apply disjoint_left.mpr
  rintro x ⟨q, hq⟩ ⟨u, hu⟩
  have heq := congrArg Prod.fst (hi (a₁ := (0, q)) (a₂ := (1, u)) (hq.trans hu.symm))
  exact (by decide : (0 : Fin 2) ≠ 1) heq

private theorem nestedPair_of_image_eq
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {C₀ C₁ D₀ D₁ : S1 → E2}
    (h₀ : R '' range C₀ = range D₀) (h₁ : R '' range C₁ = range D₁)
    (hnest : NestedPair C₀ C₁) : NestedPair D₀ D₁ := by
  obtain ⟨A, hA, hin⟩ := hnest
  refine ⟨A.trans R, ?_, ?_⟩
  · change (R ∘ A) '' sphere (0 : E2) 1 = range D₁
    rw [image_comp, hA, h₁]
  · change range D₀ ⊆ (R ∘ A) '' ball (0 : E2) 1
    rw [image_comp, ← h₀]
    exact image_mono hin



theorem exists_oppositely_nested_model_circle_pairs
    (d₁ d₂ : TerminalSaddleGeometry M P p e)
    (hmodel₁ : d₁.model = Saddle.Nested.shear (3 / 10))
    (hmodel₂ : d₂.model = Saddle.Nested.shear (3 / 10))
    (hscale : d₂.scale = d₁.scale)
    (hchart : d₂.modelChart = negativeBranchReflectedChart d₁.modelChart)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - (x 0)^2 + (x 1)^2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ C D : Fin 2 → S1 → E2,
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D i)) ∧
        Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
        Injective (fun x : Fin 2 × S1 => D x.1 x.2) ∧
        (⋃ i, range (C i)) = d₁.B (inner Real (M.v : E3) (g p) - t) ∧
        (⋃ i, range (D i)) = d₂.B (inner Real (M.v : E3) (g p) - t) ∧
        (∀ i, Saddle.toE2 (d₁.flatten (g (e (negativeLevelArc t i 0)))) ∈ range (C i)) ∧
        (∀ i, Saddle.toE2 (d₂.flatten (g (e (negativeLevelArc t i 0)))) ∈ range (D i)) ∧
        ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ i, R '' range (C i) = range (D (Equiv.swap (0 : Fin 2) 1 i))) ∧
          ((NestedPair (C 0) (C 1) ∧ NestedPair (D 1) (D 0)) ∨
            (NestedPair (C 1) (C 0) ∧ NestedPair (D 0) (D 1))) := by
  obtain ⟨ε, hε, htransition⟩ := exists_reflected_nested_model_planar_transition
    d₁ d₂ hmodel₁ hmodel₂ hscale hchart hform
  obtain ⟨r₁, δ₁, _, _, hδ₁, _, hδr₁, hcircles₁⟩ :=
    exists_nested_model_negative_branch_circle_pairs d₁ hmodel₁ hform
  obtain ⟨r₂, δ₂, _, _, hδ₂, _, hδr₂, hcircles₂⟩ :=
    exists_model_negative_branch_circle_pairs d₂ hform
  refine ⟨min ε (min δ₁ δ₂), lt_min hε (lt_min hδ₁ hδ₂), ?_⟩
  intro t ht
  have htε : t ∈ Ioc (0 : Real) ε := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have ht₁ : t ∈ Ioc (0 : Real) δ₁ :=
    ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have ht₂ : t ∈ Ioc (0 : Real) δ₂ :=
    ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨R, hR, hflip⟩ := htransition t htε
  obtain ⟨C, hC, hiC, hcoverC, hbranchC, hnest⟩ := hcircles₁ t ht₁
  obtain ⟨D, hD, hiD, hcoverD, hbranchD⟩ := hcircles₂ t ht₂
  have hctrC (i : Fin 2) :
      Saddle.toE2 (d₁.flatten (g (e (negativeLevelArc t i 0)))) ∈ range (C i) :=
    hbranchC i 0 ⟨neg_nonpos.mpr (hyperbolaRadius_pos (ht₁.2.trans_lt hδr₁)).le,
      (hyperbolaRadius_pos (ht₁.2.trans_lt hδr₁)).le⟩
  have hctrD (i : Fin 2) :
      Saddle.toE2 (d₂.flatten (g (e (negativeLevelArc t i 0)))) ∈ range (D i) :=
    hbranchD i 0 ⟨neg_nonpos.mpr (hyperbolaRadius_pos (ht₂.2.trans_lt hδr₂)).le,
      (hyperbolaRadius_pos (ht₂.2.trans_lt hδr₂)).le⟩
  let σ := Equiv.swap (0 : Fin 2) 1
  let E : Fin 2 → S1 → E2 := fun i => R ∘ C i
  let D' : Fin 2 → S1 → E2 := fun i => D (σ i)
  have hEdis : Disjoint (range (E 0)) (range (E 1)) := by
    simp only [E, range_comp]
    exact (disjoint_image_iff R.injective).mpr (circle_pair_disjoint_of_joint_injective C hiC)
  have hDdis : Disjoint (range (D' 0)) (range (D' 1)) := by
    simpa [D', σ] using (circle_pair_disjoint_of_joint_injective D hiD).symm
  have hunion : (⋃ i, range (E i)) = ⋃ i, range (D' i) := by
    simp only [E, range_comp, ← image_iUnion, hcoverC, hR, ← hcoverD]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨j, rfl⟩ := σ.surjective i
      exact mem_iUnion.mpr ⟨j, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨σ i, hi⟩
  have hmeet (i : Fin 2) : (range (E i) ∩ range (D' i)).Nonempty := by
    refine ⟨R (Saddle.toE2 (d₁.flatten (g (e (negativeLevelArc t i 0))))), ?_, ?_⟩
    · change _ ∈ range (R ∘ C i)
      rw [range_comp]
      exact mem_image_of_mem R (hctrC i)
    · rw [hflip]
      exact hctrD (σ i)
  have heq := circle_pair_ranges_eq_of_union_eq_of_inter_nonempty E D'
    (fun i => R.continuous.comp (hC i).contMDiff.continuous)
    (fun i => (hD (σ i)).contMDiff.continuous) hEdis hDdis hunion hmeet
  have hmatch (i : Fin 2) : R '' range (C i) = range (D (σ i)) := by
    simpa only [E, D', range_comp] using heq i
  refine ⟨C, D, hC, hD, hiC, hiD, hcoverC, hcoverD, hctrC, hctrD, R, hmatch, ?_⟩
  rcases hnest with h | h
  · exact Or.inl ⟨h, by simpa [σ] using nestedPair_of_image_eq R (hmatch 0) (hmatch 1) h⟩
  · exact Or.inr ⟨h, by simpa [σ] using nestedPair_of_image_eq R (hmatch 1) (hmatch 0) h⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
