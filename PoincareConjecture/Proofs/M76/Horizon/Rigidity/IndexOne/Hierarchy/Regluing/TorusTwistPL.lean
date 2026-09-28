import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.TorusWinding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLIdentity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulus
import PoincareConjecture.Proofs.M76.Rigidity.EmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL










set_option autoImplicit false
open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "T" => (Fin 2 → C)
local notation "W" => ((Fin 1 ⊕ Fin 2) → ℝ)


noncomputable def torusHandleCoordinates : H ≃ₜ (unitInterval × T) :=
  (originalIntervalCoordinates.symm.trans (iccHomeoI (-1 : ℝ) 1 (by norm_num))).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))

theorem torusHandleCoordinates_fst (x : H) :
    ((torusHandleCoordinates x).1 : ℝ) = ((x.1 : V1) 0 + 1) / 2 := by
  change ((x.1 : V1) 0 - (-1)) / (1 - (-1)) = _
  ring

theorem torusHandleCoordinates_boundary (x : H) :
    x ∈ B ↔ (torusHandleCoordinates x).1 = 0 ∨ (torusHandleCoordinates x).1 = 1 := by
  have hn : ‖(x.1 : V1)‖ = |(x.1 : V1) 0| := by
    have h : (x.1 : V1) = fun _ => (x.1 : V1) 0 := by
      funext i
      exact congrArg (x.1 : V1) (Subsingleton.elim i 0)
    rw [h, pi_norm_const, Real.norm_eq_abs]
  change (‖(x.1 : V1)‖ = 1 ∧ True) ↔ _
  rw [and_true, hn, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Subtype.ext_iff, torusHandleCoordinates_fst]
  change ((x.1 : V1) 0 = 1 ∨ (x.1 : V1) 0 = -1) ↔
    ((x.1 : V1) 0 + 1) / 2 = 0 ∨ ((x.1 : V1) 0 + 1) / 2 = 1
  constructor <;> rintro (h | h)
  · right; linarith
  · left; linarith
  · right; linarith
  · left; linarith


noncomputable def handleIntegerTwist (n : Fin 2 → ℤ) : H ≃ₜ H :=
  (torusHandleCoordinates.trans (torusIntegerTwist n)).trans torusHandleCoordinates.symm

theorem handleIntegerTwist_coordinates (n : Fin 2 → ℤ) (x : H) :
    torusHandleCoordinates (handleIntegerTwist n x) =
      torusIntegerTwist n (torusHandleCoordinates x) :=
  torusHandleCoordinates.apply_symm_apply _

theorem handleIntegerTwist_boundary (n : Fin 2 → ℤ) (x : H) (hx : x ∈ B) :
    handleIntegerTwist n x = x := by
  apply torusHandleCoordinates.injective
  rw [handleIntegerTwist_coordinates]
  exact torusIntegerTwist_boundary n _ ((torusHandleCoordinates_boundary x).mp hx)

theorem handleIntegerTwist_mk (n : Fin 2 → ℤ) (x : D1) (y : V2) :
    handleIntegerTwist n (x, QuotientAddGroup.mk y) =
      (x, QuotientAddGroup.mk (fun i => y i + p * (n i : ℝ) * (((x : V1) 0 + 1) / 2))) := by
  apply torusHandleCoordinates.injective
  rw [handleIntegerTwist_coordinates]
  apply Prod.ext
  · rfl
  · funext i
    change (y i : C) + ((p * (n i : ℝ) * ((torusHandleCoordinates
      (x, QuotientAddGroup.mk y)).1 : ℝ) : ℝ) : C) = _
    rw [torusHandleCoordinates_fst]
    exact (AddCircle.coe_add p _ _).symm

theorem handleIntegerTwist_symm (n : Fin 2 → ℤ) :
    (handleIntegerTwist n).symm = handleIntegerTwist (-n) := by
  apply Homeomorph.ext
  intro x
  apply torusHandleCoordinates.injective
  have hsymm : torusHandleCoordinates ((handleIntegerTwist n).symm x) =
      (torusIntegerTwist n).symm (torusHandleCoordinates x) := by
    exact torusHandleCoordinates.apply_symm_apply _
  rw [hsymm]
  rw [handleIntegerTwist_coordinates]
  apply Prod.ext
  · rfl
  · funext i
    simp [torusIntegerTwist, mul_neg, neg_mul, sub_eq_add_neg]


noncomputable def handleIntegerTwistAffineLift (n : Fin 2 → ℤ) : (V1 × V2) →ᴬ[ℝ] W :=
  (ContinuousLinearMap.pi fun i : Fin 1 ⊕ Fin 2 => match i with
    | Sum.inl j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ V1 V2)
    | Sum.inr j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ V1 V2) +
        (p * (n j : ℝ) / 2) •
          ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ V1 V2))).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (V1 × V2) (Sum.elim (fun _ => 0) (fun j => p * (n j : ℝ) / 2))

theorem handleIntegerTwistAffineLift_projection (n : Fin 2 → ℤ) (x : D1) (y : V2) :
    latticeCoordinateProjection (Fin 1) (Fin 2) L
      (handleIntegerTwistAffineLift n ((x : V1), y)) =
        ((handleIntegerTwist n (x, QuotientAddGroup.mk y)).1.val,
          (handleIntegerTwist n (x, QuotientAddGroup.mk y)).2) := by
  rw [handleIntegerTwist_mk]
  apply Prod.ext
  · funext i
    simp [handleIntegerTwistAffineLift, latticeCoordinateProjection]
  · apply congrArg QuotientAddGroup.mk
    funext i
    simp [handleIntegerTwistAffineLift]
    ring

private theorem standard_chartwisePLMap_of_affine_lifts
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (f : C(R, R))
    (hlift : ∀ i, ∃ v : V3 →ᴬ[ℝ] W,
      ∀ z ∈ (d i).target, ∀ hz : (d i).symm z ∈ R,
        (f ⟨(d i).symm z, hz⟩ : X) =
          latticeCoordinateProjection (Fin 1) (Fin 2) L (v z)) :
    ChartwisePLMap d d f := by
  classical
  apply chartwisePLMap_of_embedded_polyhedral_parameters (E := V3) d d hd.domain hd.domain f
  intro x
  obtain ⟨i, _, K, U, _, hK, hU, hxU, _, hUi, hUK, hKt, hKR', _, _⟩ :=
    (standard_chartwisePLMap_identity hd).coordinates x (mem_univ _)
  have hKR (z : V3) (hz : z ∈ K.space) : (d i).symm z ∈ R := by
    obtain ⟨y, _, hy⟩ := hKR' hz
    exact hy ▸ y.property
  let q : V3 → R := fun z => if hz : (d i).symm z ∈ R then ⟨(d i).symm z, hz⟩ else x
  have hqval (z : V3) (hz : z ∈ K.space) : (q z : X) = (d i).symm z := by
    simp only [q, dif_pos (hKR z hz)]
  have hq : ContinuousOn q K.space := by
    apply Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
    exact ((d i).symm.continuousOn.mono hKt).congr (fun z hz => hqval z hz)
  have hi : Topology.IsEmbedding (fun z : K.space => (d i).symm z) :=
    (d i).symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hKt)
  have hiq : Topology.IsEmbedding (fun z : K.space => q z) := by
    convert hi.codRestrict R (fun z => hKR z z.property) using 1
    funext z
    apply Subtype.ext
    exact hqval z z.property
  have hxK : d i x ∈ K.space := hUK ⟨x, hxU, rfl⟩
  let z : K.space := ⟨d i x, hxK⟩
  have hqz : q z = x := Subtype.ext ((hqval z z.property).trans ((d i).left_inv (hUi hxU)))
  have hUrange : U ⊆ range (fun z : K.space => q z) := by
    intro y hy
    refine ⟨⟨d i y, hUK ⟨y, hy, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (hqval _ (hUK ⟨y, hy, rfl⟩)).trans ((d i).left_inv (hUi hy))
  have hqPL : PolyhedralPLInCharts d (fun z => (q z : X)) K.space :=
    (polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK)
      i hKt).congr (fun z hz => (hqval z hz).symm)
  obtain ⟨v, hv⟩ := hlift i
  have hvPL : FinitePiecewiseAffineOn v K.space :=
    (K.affineOnFaces_affine v).finitePiecewiseAffineOn hK
  have hfqPL : PolyhedralPLInCharts d (fun z => (f (q z) : X)) K.space := by
    apply (hd.polyhedralPL_projection hvPL).congr
    intro z hz
    have hqeq : q z = ⟨(d i).symm z, hKR z hz⟩ := Subtype.ext (hqval z hz)
    change latticeCoordinateProjection (Fin 1) (Fin 2) L (v z) = (f (q z) : X)
    rw [hqeq]
    exact (hv z (hKt hz) _).symm
  exact ⟨K, q, z, hK, hq, hiq, hqz,
    Filter.mem_of_superset (hU.mem_nhds hxU) hUrange, hqPL, hfqPL⟩



theorem chartwisePLMap_handleIntegerTwist
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (n : Fin 2 → ℤ) :
    ChartwisePLMap d d (latticeHandleMapInDomain (Fin 1) (Fin 2) L
      ⟨handleIntegerTwist n, (handleIntegerTwist n).continuous⟩) := by
  apply standard_chartwisePLMap_of_affine_lifts hd
  intro i
  obtain ⟨a, ha⟩ := hd.inverse_formula i
  refine ⟨(handleIntegerTwistAffineLift n).comp a.toContinuousAffineMap, ?_⟩
  intro z hz hR
  have hxD : (a z).1 ∈ D1 := by
    rw [ha z hz] at hR
    exact hR.1
  let x : D1 := ⟨(a z).1, hxD⟩
  have hinput : (latticeHandleDomainEquiv (Fin 1) (Fin 2) L) ⟨(d i).symm z, hR⟩ =
      (x, QuotientAddGroup.mk (a z).2) := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (ha z hz)
    · change ((d i).symm z).2 = QuotientAddGroup.mk (a z).2
      exact congrArg Prod.snd (ha z hz)
  change ((handleIntegerTwist n ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L)
      ⟨(d i).symm z, hR⟩)).1.val,
    (handleIntegerTwist n ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L)
      ⟨(d i).symm z, hR⟩)).2) =
      latticeCoordinateProjection (Fin 1) (Fin 2) L (handleIntegerTwistAffineLift n (a z))
  rw [hinput]
  exact (handleIntegerTwistAffineLift_projection n x (a z).2).symm



theorem chartwisePLHomeomorph_handleIntegerTwist
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (n : Fin 2 → ℤ) :
    ChartwisePLHomeomorph d d
      (latticeHandleHomeomorphInDomain (Fin 1) (Fin 2) L (handleIntegerTwist n)) := by
  refine ⟨chartwisePLMap_handleIntegerTwist hd n, ?_⟩
  change ChartwisePLMap d d (latticeHandleMapInDomain (Fin 1) (Fin 2) L
    ⟨(handleIntegerTwist n).symm, (handleIntegerTwist n).symm.continuous⟩)
  simpa only [handleIntegerTwist_symm] using chartwisePLMap_handleIntegerTwist hd (-n)

end PoincareConjecture.M76.HamiltonIntervalTorus
