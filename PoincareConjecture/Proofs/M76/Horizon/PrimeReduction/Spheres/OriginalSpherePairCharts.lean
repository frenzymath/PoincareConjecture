import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ConvexCarrierWindow
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskInteriorCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse










set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private noncomputable def sphereNormalCoordinateOrder : C3 ≃ᴬ[ℝ] V3 :=
  let L : C3 ≃ₗ[ℝ] V3 :=
    { toFun := fun z => ![z.2, z.1.1, z.1.2]
      invFun := fun x => ((x 1, x 2), x 0)
      left_inv := fun _ => rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; funext i; fin_cases i <;> rfl
      map_smul' := by intro r x; funext i; fin_cases i <;> rfl }
  L.toContinuousLinearEquiv.toContinuousAffineEquiv



theorem ChartwisePLSphere.exists_pair_chart_in_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {x : X} (hx : x ∈ S) (hxQ : x ∈ Q.source) :
    ∃ B : OpenPartialHomeomorph X V3,
      x ∈ B.source ∧ B.source ⊆ Q.source ∧ B x = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ S ↔ (B y) 0 = 0 := by
  classical
  obtain ⟨J, hJ, _, hxJ, hJQ⟩ :=
    Q.open_target.exists_finite_convex_neighborhood (Q.map_source hxQ)
  obtain ⟨P, hP, hPs, hPc, hmem⟩ :=
    s.exists_finite_chart_carrier Q hQ J hJ hJQ
  have hxP : Q x ∈ P.space := (hmem _ (interior_subset hxJ)).mp
    (by simpa only [Q.left_inv hxQ] using hx)
  obtain ⟨d, q, hd, hdP, hxd, hopen⟩ :=
    s.exists_clipped_disk_neighborhood Q hQ J P hJ hJQ hP hPs hxP hxJ
  obtain ⟨b, hb, hbq⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V2
      (closedBall (0 : V2) 1) (sphere (0 : V2) 1)).exists_homeomorph hd
  have hqclosed : IsClosed q := by
    have heq : q = (fun z : closedBall (0 : V2) 1 => (b z : V3)) ''
        ((Subtype.val : closedBall (0 : V2) 1 → V2) ⁻¹' sphere (0 : V2) 1) := by
      ext z
      constructor
      · intro hz
        let t := b.symm ⟨z, hd.1 hz⟩
        refine ⟨t, ?_, congrArg Subtype.val (b.apply_symm_apply _)⟩
        exact (hbq t).mpr (by simpa only [t, b.apply_symm_apply] using hz)
      · rintro ⟨t, ht, rfl⟩
        exact (hbq t).mp ht
    rw [heq]
    exact (IsCompact.image
      (isClosed_sphere.preimage continuous_subtype_val).isCompact
      (continuous_subtype_val.comp b.continuous)).isClosed
  have hqint : interior q = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hPint : interior P.space = ∅ :=
      P.interior_space_eq_empty_of_card_le hP (by simpa using hPc)
    have hzP := interior_mono (hd.1.trans hdP) hz
    simp only [hPint, mem_empty_iff_false] at hzP
  have hfront : frontier qᶜ = q := by
    rw [frontier_compl, frontier, hqclosed.closure_eq, hqint, sdiff_empty]
  obtain ⟨H, hxH, _, _, hH, hHi, hHx, hHd⟩ :=
    HamiltonIndexOne.exists_proper_disk_interior_pair_chart (by simp) b hb
      (R := qᶜ) (fun t => by rw [hfront]; exact (hbq t).symm)
      hxd.1 (by rw [hqclosed.isOpen_compl.interior_eq]; exact hxd.2)
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
  have hxU : Q x ∈ U := (Set.ext_iff.mp hUeq ⟨Q x, hxP⟩).mpr hxd
  have hUd (z : V3) (hzP : z ∈ P.space) (hzU : z ∈ U) : z ∈ d :=
    ((Set.ext_iff.mp hUeq ⟨z, hzP⟩).mp hzU).1
  let T := H.trans sphereNormalCoordinateOrder.toHomeomorph.toOpenPartialHomeomorph
  have hT : T ∈ piecewiseAffineGroupoid V3 := by
    constructor
    · exact (locallyPiecewiseAffineOn_affine
        sphereNormalCoordinateOrder.toContinuousAffineMap isOpen_univ).comp hH
    · exact hHi.comp
        (locallyPiecewiseAffineOn_affine
          sphereNormalCoordinateOrder.symm.toContinuousAffineMap isOpen_univ)
  let V := U ∩ interior J.space
  let D := T.restrOpen V (hU.inter isOpen_interior)
  have hD : D ∈ piecewiseAffineGroupoid V3 :=
    ⟨hT.1.mono D.open_source inter_subset_left,
      hT.2.mono D.open_target inter_subset_left⟩
  let B := Q.trans D
  refine ⟨B, ⟨hxQ, ⟨hxH, mem_univ _⟩, hxU, hxJ⟩,
    fun _ hy => hy.1, ?_, ?_, ?_⟩
  · change sphereNormalCoordinateOrder (H (Q x)) = 0
    rw [hHx]
    funext i
    fin_cases i <;> rfl
  · intro i
    simpa only [B, OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hQ i) hD
  · intro y hy
    have hyJ : Q y ∈ J.space := interior_subset hy.2.2.2
    have hyPd : Q y ∈ P.space ↔ Q y ∈ d :=
      ⟨fun h => hUd _ h hy.2.2.1, fun h => hdP h⟩
    have hyS : y ∈ S ↔ Q y ∈ P.space := by
      simpa only [Q.left_inv hy.1] using hmem (Q y) hyJ
    exact hyS.trans (hyPd.trans (hHd (Q y) hy.2.1.1))



theorem ChartwisePLSphere.exists_pair_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (e i).source) {x : X} (hx : x ∈ S) :
    ∃ B : OpenPartialHomeomorph X V3, x ∈ B.source ∧ B x = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ S ↔ (B y) 0 = 0 := by
  obtain ⟨i, hi⟩ := hcover x hx
  obtain ⟨B, hxB, _, hBx, hB, hBS⟩ :=
    s.exists_pair_chart_in_chart (e i) (fun j => hcompat j i) hx hi
  exact ⟨B, hxB, hBx, hB, hBS⟩

end PoincareConjecture.M76
