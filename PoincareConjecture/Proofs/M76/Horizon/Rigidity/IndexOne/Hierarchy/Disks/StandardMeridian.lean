import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardSlabCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardFrontier
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

private theorem standardSlabCoordinates_ambient (a b : ℝ) (hshort : b < a + p)
    (z : (D1 × C) × Icc a b) :
    standardAmbientCoordinates (standardSlabCoordinates a b hshort z) =
      (((z.1.1 : V1), z.1.2), ((z.2 : ℝ) : C)) := by
  change ((_, (hamiltonLowerLatticePiEquiv (Fin 2))
    ((hamiltonLowerLatticePiEquiv (Fin 2)).symm ![z.1.2, ((z.2 : ℝ) : C)]) 0),
    (hamiltonLowerLatticePiEquiv (Fin 2))
    ((hamiltonLowerLatticePiEquiv (Fin 2)).symm ![z.1.2, ((z.2 : ℝ) : C)]) 1) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem standardSlabCoordinates_frontier (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (z : (D1 × C) × Icc a b) :
    (standardSlabCoordinates a b hshort z : X) ∈
        frontier (sourceSlab (ContinuousMap.id H) a b) ↔
      ‖(z.1.1 : V1)‖ = 1 ∨ (z.2 : ℝ) = a ∨ (z.2 : ℝ) = b := by
  let c := (a + b - p) / 2
  have hca : c < a := by dsimp [c]; linarith
  have hbc : b < c + p := by dsimp [c]; linarith
  rw [frontier_standard_sourceSlab hca hab.le hbc]
  have hslab := (standardSlabCoordinates a b hshort z).property
  rw [mem_union, mem_inter_iff, and_iff_right hslab, mem_union]
  rw [standard_domain_eq_coordinate_preimage, ← standardAmbientCoordinates.preimage_frontier,
    frontier_prod_univ_eq, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero,
    standard_sourceSurface_eq_coordinate_preimage,
    standard_sourceSurface_eq_coordinate_preimage]
  simp only [mem_preimage, standardSlabCoordinates_ambient, mem_prod, mem_univ,
    and_true, mem_sphere_zero_iff_norm, z.1.1.property, true_and, mem_singleton_iff]
  have hz : (z.2 : ℝ) ∈ Ico a (a + p) := ⟨z.2.property.1, z.2.property.2.trans_lt hshort⟩
  rw [AddCircle.coe_eq_coe_iff_of_mem_Ico hz ⟨le_rfl, by linarith⟩,
    AddCircle.coe_eq_coe_iff_of_mem_Ico hz ⟨hab.le, hshort⟩]

private theorem norm_pair (s t : ℝ) : ‖(![s, t] : V2)‖ = max |s| |t| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (abs_nonneg s) (le_max_left _ _))).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (norm_le_pi_norm (![s, t] : V2) 0)
      (norm_le_pi_norm (![s, t] : V2) 1)

private theorem norm_one_coordinate (v : V1) : ‖v‖ = |v 0| := by
  have hv : v = fun _ => v 0 := by funext i; congr 1; exact Subsingleton.elim _ _
  rw [hv, pi_norm_const, Real.norm_eq_abs]

private noncomputable def meridianHeight (a b t : ℝ) : ℝ := (b - a) * (t + 1) / 2 + a

private noncomputable def meridianHeightInv (a b t : ℝ) : ℝ := 2 * (t - a) / (b - a) - 1

private theorem meridianHeight_bounds {a b t : ℝ} (hab : a < b)
    (ht : |t| ≤ 1) : meridianHeight a b t ∈ Icc a b := by
  dsimp [meridianHeight]
  have ht' := abs_le.mp ht
  constructor <;> nlinarith

private theorem meridianHeightInv_bounds {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) : |meridianHeightInv a b t| ≤ 1 := by
  dsimp [meridianHeightInv]
  apply abs_le.mpr
  constructor
  · have h : 0 ≤ 2 * (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) (by linarith)
    linarith
  · have h : 2 * (t - a) / (b - a) ≤ 2 := (div_le_iff₀ (by linarith : 0 < b-a)).mpr (by linarith [ht.2])
    linarith

private theorem meridianHeightInv_height {a b : ℝ} (hab : a < b) (t : ℝ) :
    meridianHeightInv a b (meridianHeight a b t) = t := by
  dsimp [meridianHeightInv, meridianHeight]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

private theorem meridianHeightInv_edge {a b t : ℝ} (hab : a < b) :
    |meridianHeightInv a b t| = 1 ↔ t = a ∨ t = b := by
  rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
  dsimp [meridianHeightInv]
  have hne : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  constructor
  · rintro (h | h)
    · right
      have he : 2*(t-a)/(b-a) = 2 := by linarith
      have := (div_eq_iff hne).mp he
      linarith
    · left
      have he : 2*(t-a)/(b-a) = 0 := by linarith
      have := (div_eq_iff hne).mp he
      linarith
  · rintro (rfl | rfl)
    · right; simp
    · left; rw [mul_div_cancel_right₀ _ hne]; norm_num

private noncomputable def meridianRectangle (a b : ℝ) (hab : a < b) :
    C(D2, (D1 × C) × Icc a b) where
  toFun x := ((⟨fun _ => x.val 0, by
    rw [mem_closedBall_zero_iff, pi_norm_const]
    exact (norm_le_pi_norm x.val 0).trans (mem_closedBall_zero_iff.mp x.property)⟩, 0),
      ⟨meridianHeight a b (x.val 1), meridianHeight_bounds hab
        ((norm_le_pi_norm x.val 1).trans (mem_closedBall_zero_iff.mp x.property))⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.prodMk
      · apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact (continuous_apply 0).comp continuous_subtype_val
      · exact continuous_const
    · apply Continuous.subtype_mk
      dsimp [meridianHeight]
      have hc : Continuous (fun x : D2 => x.val 1) :=
        (continuous_apply 1).comp continuous_subtype_val
      exact ((continuous_const.mul (hc.add continuous_const)).div_const 2).add continuous_const

private noncomputable def meridianRectangleProjection (a b : ℝ) :
    C((D1 × C) × Icc a b, V2) where
  toFun z := ![(z.1.1 : V1) 0, meridianHeightInv a b (z.2 : ℝ)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun z : (D1 × C) × Icc a b => (z.1.1 : V1) 0)
      exact (continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst.fst)
    · dsimp [meridianHeightInv]
      fun_prop

private theorem meridianRectangleProjection_left (a b : ℝ) (hab : a < b) (x : D2) :
    meridianRectangleProjection a b (meridianRectangle a b hab x) = x.val := by
  funext i
  fin_cases i
  · rfl
  · exact meridianHeightInv_height hab _

private theorem meridianRectangleProjection_sphere (a b : ℝ) (hab : a < b)
    (z : (D1 × C) × Icc a b) :
    meridianRectangleProjection a b z ∈ Q2 ↔
      ‖(z.1.1 : V1)‖ = 1 ∨ (z.2 : ℝ) = a ∨ (z.2 : ℝ) = b := by
  change ![(z.1.1 : V1) 0, meridianHeightInv a b (z.2 : ℝ)] ∈ Q2 ↔ _
  rw [mem_sphere_zero_iff_norm, norm_pair, norm_one_coordinate]
  have hx : |(z.1.1 : V1) 0| ≤ 1 :=
    (norm_le_pi_norm (z.1.1 : V1) 0).trans (mem_closedBall_zero_iff.mp z.1.1.property)
  have hy := meridianHeightInv_bounds hab z.2.property
  rw [max_eq_iff, ← meridianHeightInv_edge hab]
  constructor
  · tauto
  · rintro (h | h)
    · exact Or.inl ⟨h, by rw [h]; exact hy⟩
    · exact Or.inr ⟨h, by rw [h]; exact hx⟩



theorem exists_standard_meridian (a b : ℝ) (hab : a < b) (hshort : b < a + p) :
    ∃ (f : C(D2, sourceSlab (ContinuousMap.id H) a b))
      (gamma : C(Q2, frontier (sourceSlab (ContinuousMap.id H) a b)))
      (r : C(frontier (sourceSlab (ContinuousMap.id H) a b), Q2)),
      (∀ x : Q2, (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = gamma x) ∧
      (∀ x : Q2, r (gamma x) = x) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  let T := standardSlabCoordinates a b hshort
  let j : C(Q2, D2) := ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let f : C(D2, sourceSlab (ContinuousMap.id H) a b) :=
    (⟨T, T.continuous⟩ : C(_, _)).comp (meridianRectangle a b hab)
  have hf : ∀ x : Q2, (f (j x) : X) ∈
      frontier (sourceSlab (ContinuousMap.id H) a b) := by
    intro x
    apply (standardSlabCoordinates_frontier a b hab hshort _).mpr
    apply (meridianRectangleProjection_sphere a b hab _).mp
    rw [meridianRectangleProjection_left]
    exact x.property
  let gamma : C(Q2, frontier (sourceSlab (ContinuousMap.id H) a b)) :=
    ⟨fun x => ⟨f (j x), hf x⟩,
      (continuous_subtype_val.comp (f.continuous.comp j.continuous)).subtype_mk _⟩
  have hclosed : IsClosed (sourceSlab (ContinuousMap.id H) a b) := by
    rw [standard_sourceSlab_eq_coordinate_preimage]
    exact ((isClosed_closedBall.prod isClosed_univ).prod
      (AddCircle.isCompact_closedIntervalArc p a b).isClosed).preimage
        standardAmbientCoordinates.continuous
  let k : C(frontier (sourceSlab (ContinuousMap.id H) a b),
      sourceSlab (ContinuousMap.id H) a b) :=
    ⟨fun x => ⟨x, hclosed.frontier_subset x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let r0 := (meridianRectangleProjection a b).comp
    ((⟨T.symm, T.symm.continuous⟩ : C(_, _)).comp k)
  have hr0 : ∀ x, r0 x ∈ Q2 := by
    intro x
    apply (meridianRectangleProjection_sphere a b hab _).mpr
    apply (standardSlabCoordinates_frontier a b hab hshort _).mp
    change (T (T.symm (k x)) : X) ∈ _
    rw [T.apply_symm_apply]
    exact x.property
  let r : C(frontier (sourceSlab (ContinuousMap.id H) a b), Q2) :=
    ⟨fun x => ⟨r0 x, hr0 x⟩, r0.continuous.subtype_mk _⟩
  have hleft : ∀ x : Q2, r (gamma x) = x := by
    intro x
    apply Subtype.ext
    change meridianRectangleProjection a b
      (T.symm (T (meridianRectangle a b hab (j x)))) = x.val
    rw [T.symm_apply_apply, meridianRectangleProjection_left]
    rfl
  exact ⟨f, gamma, r, fun _ => rfl, hleft,
    Dehn.squareRimLoop_map_class_ne_one_of_retraction gamma r hleft⟩



noncomputable def standardSlabMeridianCoordinates (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) : (D2 × C) ≃ₜ sourceSlab (ContinuousMap.id H) a b := by
  let F := meridianRectangle a b hab
  let P := meridianRectangleProjection a b
  have hP (z : (D1 × C) × Icc a b) : P z ∈ D2 := by
    rw [mem_closedBall_zero_iff]
    change ‖(![(z.1.1 : V1) 0, meridianHeightInv a b (z.2 : ℝ)] : V2)‖ ≤ 1
    rw [norm_pair]
    exact max_le
      ((norm_le_pi_norm (z.1.1 : V1) 0).trans (mem_closedBall_zero_iff.mp z.1.1.property))
      (meridianHeightInv_bounds hab z.2.property)
  let rect : (D2 × C) ≃ₜ ((D1 × C) × Icc a b) := {
    toFun := fun z => (((F z.1).1.1, z.2), (F z.1).2)
    invFun := fun z => (⟨P z, hP z⟩, z.1.2)
    left_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change P (((F z.1).1.1, z.2), (F z.1).2) = z.1.val
        exact meridianRectangleProjection_left a b hab z.1
      · rfl
    right_inv := by
      intro z
      apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          funext i
          change (z.1.1 : V1) 0 = (z.1.1 : V1) i
          exact congrArg z.1.1.val (Subsingleton.elim _ _)
        · rfl
      · apply Subtype.ext
        change meridianHeight a b (meridianHeightInv a b z.2) = z.2
        dsimp [meridianHeight, meridianHeightInv]
        field_simp [ne_of_gt (sub_pos.mpr hab)]
        ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact rect.trans (standardSlabCoordinates a b hshort)



theorem standardSlabMeridianCoordinates_frontier (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (z : D2 × C) :
    (standardSlabMeridianCoordinates a b hab hshort z : X) ∈
      frontier (sourceSlab (ContinuousMap.id H) a b) ↔ (z.1 : V2) ∈ Q2 := by
  rw [standardSlabMeridianCoordinates, Homeomorph.trans_apply,
    standardSlabCoordinates_frontier a b hab hshort,
    ← meridianRectangleProjection_sphere a b hab]
  change meridianRectangleProjection a b (meridianRectangle a b hab z.1) ∈ Q2 ↔ _
  rw [meridianRectangleProjection_left]



noncomputable def standardSlabBoundaryCoordinates (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) : (Q2 × C) ≃ₜ frontier (sourceSlab (ContinuousMap.id H) a b) := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  let T := standardSlabMeridianCoordinates a b hab hshort
  let inc : C(Q2, D2) := ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩, by fun_prop⟩
  have hclosed : IsClosed (sourceSlab (ContinuousMap.id H) a b) :=
    (sourceSlab_isCompact (ContinuousMap.id H) a b).isClosed
  let toSlab : C(frontier (sourceSlab (ContinuousMap.id H) a b),
      sourceSlab (ContinuousMap.id H) a b) := ContinuousMap.inclusion hclosed.frontier_subset
  have hboundary (z : frontier (sourceSlab (ContinuousMap.id H) a b)) :
      ((T.symm (toSlab z)).1 : V2) ∈ Q2 := by
    apply (standardSlabMeridianCoordinates_frontier a b hab hshort _).mp
    change (T (T.symm (toSlab z)) : X) ∈ _
    rw [T.apply_symm_apply]
    exact z.property
  exact {
    toFun := fun z => ⟨T (inc z.1, z.2),
      (standardSlabMeridianCoordinates_frontier a b hab hshort _).mpr z.1.property⟩
    invFun := fun z => (⟨(T.symm (toSlab z)).1, hboundary z⟩, (T.symm (toSlab z)).2)
    left_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change ((T.symm (T (inc z.1, z.2))).1 : V2) = z.1
        rw [T.symm_apply_apply]
        rfl
      · change (T.symm (T (inc z.1, z.2))).2 = z.2
        rw [T.symm_apply_apply]
    right_inv := by
      intro z
      apply Subtype.ext
      change (T ((T.symm (toSlab z)).1, (T.symm (toSlab z)).2) : X) = z
      rw [Prod.eta, T.apply_symm_apply]
      rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }


theorem standardSlabMeridianCoordinates_coe (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (x : D2) (t : ℝ) :
    (standardSlabMeridianCoordinates a b hab hshort (x, (t : C)) : X) =
      ((fun _ => x.val 0), QuotientAddGroup.mk ![t, (b - a) * (x.val 1 + 1) / 2 + a]) := by
  change ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
    (hamiltonOneHierarchyCoordinates.symm
      ((⟨fun _ => x.val 0, _⟩, (t : C)),
        (((b - a) * (x.val 1 + 1) / 2 + a : ℝ) : C))) : X) = _
  rw [hamiltonOneHierarchyCoordinates_symm_coe]
  rfl

theorem standardSlabBoundaryCoordinates_coe (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (x : Q2) (t : ℝ) :
    (standardSlabBoundaryCoordinates a b hab hshort (x, (t : C)) : X) =
      ((fun _ => x.val 0), QuotientAddGroup.mk ![t, (b - a) * (x.val 1 + 1) / 2 + a]) :=
  standardSlabMeridianCoordinates_coe a b hab hshort
    ⟨x, sphere_subset_closedBall x.property⟩ t

end PoincareConjecture.M76.HamiltonIntervalTorus
