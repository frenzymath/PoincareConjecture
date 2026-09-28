import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.OldBoundaryStrips
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.ExactBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourcePhaseSets
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Interior
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing











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



theorem marked_phase_homeomorph_fixed_on_old_boundary
    (phi psi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (G : (ContinuousMap.id H).HomotopyRel psi B)
    (A : Ann ≃ₜ sourceSurface phi theta) (A' : Ann ≃ₜ sourceSurface psi theta)
    (scale : C32 ≃ₜ C)
    (hA : ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) (scale z) : X))
    (hA' : ∀ side z, (A' (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle psi theta G (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) (scale z) : X))
    (x : sourceSurface phi theta) (hx : (x : X) ∈ frontier R) :
    (A' (A.symm x) : X) = x := by
  obtain ⟨side, c, hc⟩ := exists_original_boundaryCircle_of_mem_rim phi theta F
    ⟨x.property, hx⟩
  have hAx : A (Dehn.annulusRimPoint side (scale.symm c)) = x := by
    apply Subtype.ext
    rw [hA, scale.apply_symm_apply]
    exact hc
  rw [← hAx, A.symm_apply_apply, hA', hA]
  rfl



theorem old_sourceSlab_eq_of_relative_maps
    (phi psi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (G : (ContinuousMap.id H).HomotopyRel psi B) :
    sourceSlab phi a b ∩ frontier R = sourceSlab psi a b ∩ frontier R := by
  let E := (oldSlabCoordinates phi a b F).trans (oldSlabCoordinates psi a b G).symm
  have hE (x : ↥(sourceSlab phi a b ∩ frontier R)) : (E x : X) = x := by
    change ((oldSlabCoordinates psi a b G).symm (oldSlabCoordinates phi a b F x) : X) = x
    rw [oldSlabCoordinates_symm_original_point]
    exact congrArg Subtype.val ((oldSlabCoordinates phi a b F).symm_apply_apply x)
  apply Subset.antisymm
  · intro x hx
    have hh := (E ⟨x, hx⟩).property
    change (E ⟨x, hx⟩ : X) ∈ sourceSlab psi a b ∩ frontier R at hh
    rwa [hE] at hh
  · intro x hx
    obtain ⟨y, hy⟩ := E.surjective ⟨x, hx⟩
    have hxy : (y : X) = x := (hE y).symm.trans (congrArg Subtype.val hy)
    exact hxy ▸ y.property



theorem exists_marked_slab_frontier_homeomorph
    (phi psi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (G : (ContinuousMap.id H).HomotopyRel psi B)
    (a b : ℝ) (hne : (a : C) ≠ (b : C))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfront' : frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
      (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (A' : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface psi theta)
    (scale : C32 ≃ₜ C)
    (hA : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)), ∀ side z,
      (A theta htheta (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side) (scale z) : X))
    (hA' : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)), ∀ side z,
      (A' theta htheta (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle psi theta G (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side) (scale z) : X)) :
    ∃ E : ↥(frontier (sourceSlab phi a b)) ≃ₜ ↥(frontier (sourceSlab psi a b)),
      (∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x) ∧
      ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (x : sourceSurface phi theta),
        (E ⟨x, hfront.symm ▸ Or.inr (by
          rcases htheta with rfl | rfl
          · exact Or.inl x.property
          · exact Or.inr x.property)⟩ : X) = A' theta htheta ((A theta htheta).symm x) := by
  classical
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have hdis (f : C(H, H)) : Disjoint (sourceSurface f (a : C)) (sourceSurface f (b : C)) := by
    rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    exact disjoint_left.mpr fun x hx hy => hne (hx.2.symm.trans hy.2)
  let ea := (A (a : C) (Or.inl rfl)).symm.trans (A' (a : C) (Or.inl rfl))
  let eb := (A (b : C) (Or.inr rfl)).symm.trans (A' (b : C) (Or.inr rfl))
  obtain ⟨Eph, hEa, hEb⟩ := Homeomorph.exists_union_of_compact
    (sourceSurface_isCompact phi (a : C)) (sourceSurface_isCompact phi (b : C)) ea eb
    (fun x => iff_of_false
      (fun hx => disjoint_left.mp (hdis phi) x.property hx)
      (fun hx => disjoint_left.mp (hdis psi) (ea x).property hx))
    (fun x hx hy => (disjoint_left.mp (hdis phi) hx hy).elim)
  let S := sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)
  let S' := sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)
  let O := sourceSlab phi a b ∩ frontier R
  have hOeq : O = sourceSlab psi a b ∩ frontier R := old_sourceSlab_eq_of_relative_maps phi psi a b F G
  have hfix (x : S) (hx : (x : X) ∈ frontier R) : (Eph x : X) = x := by
    rcases x.property with ha | hb
    · rw [hEa ⟨x, ha⟩]
      exact marked_phase_homeomorph_fixed_on_old_boundary phi psi (a : C) F G
        (A (a : C) (Or.inl rfl)) (A' (a : C) (Or.inl rfl)) scale
          (hA _ (Or.inl rfl)) (hA' _ (Or.inl rfl)) ⟨x, ha⟩ hx
    · rw [hEb ⟨x, hb⟩]
      exact marked_phase_homeomorph_fixed_on_old_boundary phi psi (b : C) F G
        (A (b : C) (Or.inr rfl)) (A' (b : C) (Or.inr rfl)) scale
          (hA _ (Or.inr rfl)) (hA' _ (Or.inr rfl)) ⟨x, hb⟩ hx
  have hphaseOld (x : S) : (x : X) ∈ frontier R ↔ (Eph x : X) ∈ frontier R := by
    constructor
    · intro hx
      rwa [hfix x hx]
    · intro hx
      rcases x.property with ha | hb
      · have hx' : (ea ⟨x, ha⟩ : X) ∈ frontier R := by rwa [hEa ⟨x, ha⟩] at hx
        have hh := marked_phase_homeomorph_fixed_on_old_boundary psi phi (a : C) G F
          (A' (a : C) (Or.inl rfl)) (A (a : C) (Or.inl rfl)) scale
            (hA' _ (Or.inl rfl)) (hA _ (Or.inl rfl))
          (ea ⟨x, ha⟩) hx'
        have heq : (ea ⟨x, ha⟩ : X) = x := by
          simpa only [ea, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
            Homeomorph.apply_symm_apply] using hh.symm
        rwa [heq] at hx'
      · have hx' : (eb ⟨x, hb⟩ : X) ∈ frontier R := by rwa [hEb ⟨x, hb⟩] at hx
        have hh := marked_phase_homeomorph_fixed_on_old_boundary psi phi (b : C) G F
          (A' (b : C) (Or.inr rfl)) (A (b : C) (Or.inr rfl)) scale
            (hA' _ (Or.inr rfl)) (hA _ (Or.inr rfl))
          (eb ⟨x, hb⟩) hx'
        have heq : (eb ⟨x, hb⟩ : X) = x := by
          simpa only [eb, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
            Homeomorph.apply_symm_apply] using hh.symm
        rwa [heq] at hx'
  have hSO (x : S) : (x : X) ∈ O ↔ (Eph x : X) ∈ O := by
    constructor
    · intro hx
      rwa [hfix x hx.2]
    · intro hx
      have hxR := (hphaseOld x).mpr hx.2
      rwa [hfix x hxR] at hx
  have hOc : IsCompact O := (sourceSlab_isCompact phi a b).inter_right isClosed_frontier
  obtain ⟨E0, hEph, hEO⟩ := Homeomorph.exists_union_of_compact
    ((sourceSurface_isCompact phi (a : C)).union (sourceSurface_isCompact phi (b : C)))
    hOc Eph (Homeomorph.refl O) hSO (fun x hxS hxO => hfix ⟨x, hxS⟩ hxO.2)
  have hsource : frontier (sourceSlab phi a b) = S ∪ O := by rw [hfront]; exact union_comm _ _
  have htarget : S' ∪ O = frontier (sourceSlab psi a b) := by
    rw [hOeq, hfront']
    exact union_comm _ _
  let E := (Homeomorph.setCongr hsource).trans (E0.trans (Homeomorph.setCongr htarget))
  refine ⟨E, ?_, ?_⟩
  · intro x hxR
    have hxO : (x : X) ∈ O :=
      ⟨(sourceSlab_isCompact phi a b).isClosed.frontier_subset x.property, hxR⟩
    exact hEO ⟨x, hxO⟩
  · intro theta htheta x
    rcases htheta with rfl | rfl
    · exact (hEph ⟨x, Or.inl x.property⟩).trans (hEa x)
    · exact (hEph ⟨x, Or.inr x.property⟩).trans (hEb x)

end PoincareConjecture.M76.HamiltonIntervalTorus
