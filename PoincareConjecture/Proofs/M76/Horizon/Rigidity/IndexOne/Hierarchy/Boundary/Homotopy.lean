import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalToStandard
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.ClosedPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.SourceCorrection

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L

private instance : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
  (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space

noncomputable def slabFrontierHandleInclusion (phi : C(H, H)) (a b : ℝ) :
    C(frontier (sourceSlab phi a b), H) where
  toFun x := Q ⟨x, sourceSlab_subset phi a b
    ((sourceSlab_isCompact phi a b).isClosed.frontier_subset x.property)⟩
  continuous_toFun := by fun_prop

private theorem inverse_annulus_mem_rims
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (A : Ann ≃ₜ sourceSurface phi theta) (scale : C32 ≃ₜ C)
    (hA : ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) (scale z) : X))
    (x : sourceSurface phi theta) (hx : (x : X) ∈ frontier R) :
    A.symm x ∈ Dehn.annulusRims := by
  obtain ⟨side, c, hc⟩ := exists_original_boundaryCircle_of_mem_rim phi theta F ⟨x.property, hx⟩
  have hAx : A (Dehn.annulusRimPoint side (scale.symm c)) = x := by
    apply Subtype.ext
    rw [hA, scale.apply_symm_apply]
    exact hc
  rw [← hAx, A.symm_apply_apply]
  cases side
  · exact Or.inl ⟨scale.symm c, rfl⟩
  · exact Or.inr ⟨scale.symm c, rfl⟩

theorem exists_original_to_standard_frontier_homotopy
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (hA : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)), ∀ side z,
      (A theta htheta (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
            (by norm_num) (by norm_num) z) : X))
    (hhom : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)),
      Nonempty ((sourceAnnulusHandleMap phi theta (A theta htheta)).HomotopyRel
        (sourceAnnulusHandleMap (ContinuousMap.id H) theta (standardTargetAnnulus theta))
        Dehn.annulusRims)) :
    ∃ E : ↥(frontier (sourceSlab phi a b)) ≃ₜ
        ↥(frontier (sourceSlab (ContinuousMap.id H) a b)),
      (∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x) ∧
      (∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (x : sourceSurface phi theta),
        (E ⟨x, hfront.symm ▸ Or.inr (by
          rcases htheta with rfl | rfl
          · exact Or.inl x.property
          · exact Or.inr x.property)⟩ : X) =
          standardTargetAnnulus theta ((A theta htheta).symm x)) ∧
      Nonempty ((phi.comp (slabFrontierHandleInclusion phi a b)).HomotopyRel
        ((slabFrontierHandleInclusion (ContinuousMap.id H) a b).comp ⟨E, E.continuous⟩)
        {x | (x : X) ∈ frontier R}) := by
  classical
  obtain ⟨E, hEold, hEphase⟩ := exists_original_to_standard_frontier_homeomorph
    phi F ha hab hb hfront A hA
  let T (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C)) :=
    Classical.choice (hhom theta htheta)
  let W (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C)) :
      C(unitInterval × sourceSurface phi theta, H) :=
    (T theta htheta).toHomotopy.toContinuousMap.comp
      ⟨fun z => (z.1, (A theta htheta).symm z.2), by fun_prop⟩
  have hWzero (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
      (x : sourceSurface phi theta) :
      W theta htheta (0, x) = phi (Q ⟨x, sourceSurface_subset phi theta x.property⟩) := by
    change T theta htheta (0, (A theta htheta).symm x) = _
    rw [(T theta htheta).apply_zero]
    change phi (Q ⟨A theta htheta ((A theta htheta).symm x), _⟩) = _
    apply congrArg phi
    apply congrArg Q
    exact Subtype.ext (congrArg (fun y : sourceSurface phi theta => (y : X))
      ((A theta htheta).apply_symm_apply x))
  have hWone (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
      (x : sourceSurface phi theta) :
      W theta htheta (1, x) = Q ⟨standardTargetAnnulus theta ((A theta htheta).symm x),
        sourceSurface_subset (ContinuousMap.id H) theta
          (standardTargetAnnulus theta ((A theta htheta).symm x)).property⟩ := by
    change T theta htheta (1, (A theta htheta).symm x) = _
    rw [(T theta htheta).apply_one]
    rfl
  have hWold (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
      (t : unitInterval) (x : sourceSurface phi theta) (hx : (x : X) ∈ frontier R) :
      W theta htheta (t, x) = phi (Q ⟨x, sourceSurface_subset phi theta x.property⟩) := by
    change T theta htheta (t, (A theta htheta).symm x) = _
    rw [(T theta htheta).eq_fst t (inverse_annulus_mem_rims phi theta F (A theta htheta)
      (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num) (by norm_num))
      (hA theta htheta) x hx)]
    change phi (Q ⟨A theta htheta ((A theta htheta).symm x), _⟩) = _
    apply congrArg phi
    apply congrArg Q
    exact Subtype.ext (congrArg (fun y : sourceSurface phi theta => (y : X))
      ((A theta htheta).apply_symm_apply x))
  have hne : (a : C) ≠ (b : C) := by
    let : Fact (0 < p) := ⟨by norm_num⟩
    intro hh
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico c (c + p) from ⟨ha.le, hab.trans hb⟩)
      (show b ∈ Ico c (c + p) from ⟨(ha.trans hab).le, hb⟩)).mp hh)
  have hdis : Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) := by
    rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    exact disjoint_left.mpr fun x hx hy => hne (hx.2.symm.trans hy.2)
  obtain ⟨Wph, hWa, hWb⟩ := ContinuousMap.exists_product_union_of_isClosed
    (sourceSurface_isCompact phi (a : C)).isClosed (sourceSurface_isCompact phi (b : C)).isClosed
    (W (a : C) (Or.inl rfl)) (W (b : C) (Or.inr rfl))
    (fun _ _ hx hy => (disjoint_left.mp hdis hx hy).elim)
  let S := sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)
  let O := sourceSlab phi a b ∩ frontier R
  let old : C(unitInterval × O, H) := ⟨fun z => phi (Q
    ⟨z.2, sourceSlab_subset phi a b z.2.property.1⟩), by fun_prop⟩
  obtain ⟨Full, hFullPhase, hFullOld⟩ := ContinuousMap.exists_product_union_of_isClosed
    ((sourceSurface_isCompact phi (a : C)).union (sourceSurface_isCompact phi (b : C))).isClosed
    ((sourceSlab_isCompact phi a b).inter_right isClosed_frontier).isClosed Wph old (by
      intro t x hxS hxO
      rcases hxS with hxa | hxb
      · rw [hWa t ⟨x, hxa⟩]
        exact hWold (a : C) (Or.inl rfl) t ⟨x, hxa⟩ hxO.2
      · rw [hWb t ⟨x, hxb⟩]
        exact hWold (b : C) (Or.inr rfl) t ⟨x, hxb⟩ hxO.2)
  have hdecomp : frontier (sourceSlab phi a b) = S ∪ O := by
    rw [hfront]
    exact union_comm _ _
  let j := Homeomorph.setCongr hdecomp
  let V : C(unitInterval × frontier (sourceSlab phi a b), H) :=
    Full.comp ⟨fun z => (z.1, j z.2), by fun_prop⟩
  have hVold (t : unitInterval) (x : frontier (sourceSlab phi a b))
      (hx : (x : X) ∈ frontier R) : V (t, x) = phi (slabFrontierHandleInclusion phi a b x) := by
    have hxO : (x : X) ∈ O :=
      ⟨(sourceSlab_isCompact phi a b).isClosed.frontier_subset x.property, hx⟩
    exact hFullOld t ⟨x, hxO⟩
  have hVphase (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
      (t : unitInterval) (x : frontier (sourceSlab phi a b))
      (hx : (x : X) ∈ sourceSurface phi theta) : V (t, x) = W theta htheta (t, ⟨x, hx⟩) := by
    rcases htheta with rfl | rfl
    · exact (hFullPhase t ⟨x, Or.inl hx⟩).trans (hWa t ⟨x, hx⟩)
    · exact (hFullPhase t ⟨x, Or.inr hx⟩).trans (hWb t ⟨x, hx⟩)
  refine ⟨E, hEold, hEphase, ⟨{
    toFun := V
    continuous_toFun := V.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    rcases hfront.subset x.property with hx | hx | hx
    · exact hVold 0 x hx.2
    · exact (hVphase (a : C) (Or.inl rfl) 0 x hx).trans (hWzero (a : C) (Or.inl rfl) ⟨x, hx⟩)
    · exact (hVphase (b : C) (Or.inr rfl) 0 x hx).trans (hWzero (b : C) (Or.inr rfl) ⟨x, hx⟩)
  · intro x
    have hpoint (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (hx : (x : X) ∈ sourceSurface phi theta) :
        V (1, x) = slabFrontierHandleInclusion (ContinuousMap.id H) a b (E x) := by
      rw [hVphase theta htheta 1 x hx, hWone]
      apply congrArg Q
      apply Subtype.ext
      exact (hEphase theta htheta ⟨x, hx⟩).symm
    rcases hfront.subset x.property with hx | hx | hx
    · rw [hVold 1 x hx.2]
      have hxB : slabFrontierHandleInclusion phi a b x ∈ B := by
        exact (Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary
          (Fin 1) (Fin 2) L) _).mpr hx.2
      have hfix : phi (slabFrontierHandleInclusion phi a b x) =
          slabFrontierHandleInclusion phi a b x :=
        (F.apply_one _).symm.trans (F.eq_fst 1 hxB)
      rw [hfix]
      apply congrArg Q
      apply Subtype.ext
      exact (hEold x hx.2).symm
    · exact hpoint (a : C) (Or.inl rfl) hx
    · exact hpoint (b : C) (Or.inr rfl) hx
  · intro t x hx
    exact hVold t x hx

end PoincareConjecture.M76.HamiltonIntervalTorus
