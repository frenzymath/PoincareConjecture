import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology
import PoincareLib.AlgebraicTopology.FundamentalGroup.TopologicalAdapters
import PoincareLib.Topology.Homotopy.Sphere.SphereConnectivity
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible

/-! Adapted from Mapher `PoincareMT/Proofs/M54/ConnectedSum/Coordinates.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Ball and collar coordinates in Proposition 15.3

The frozen smooth maps give homeomorphisms of their displayed domains.
Their spherical annuli and collar halves are simply connected, using the
published M02 sphere theorem. Sources: Morgan--Tian Proposition 15.3,
pp. 357-358; Hatcher Theorem 1.20 and Proposition 1.26(b), pp. 43-50.
-/

set_option autoImplicit false

open Set Metric
open scoped Topology Manifold ContDiff

universe u

namespace PoincareMT

namespace SurgeryRegionEquivalence

/-- The subspace homeomorphism underlying a smooth region equivalence
in Proposition 15.3 (pp. 357-358). -/
def toHomeomorph {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}
    (e : SurgeryRegionEquivalence A B U V) : U ≃ₜ V :=
  Homeomorph.ofSetInverse e.map e.inverse U V e.map_smooth.continuousOn
    e.inverse_smooth.continuousOn
    (fun _ hx => e.map_image.subset (mem_image_of_mem _ hx))
    (fun _ hy => e.inverse_image.subset (mem_image_of_mem _ hy))
    e.left_inverse e.right_inverse

end SurgeryRegionEquivalence

namespace SurgeryCoordinates

/-- The unit two-sphere in the surgery collar is simply connected, as in
MT Proposition 15.3, pp. 357-358; this reuses the published M02 sphere calculation. -/
theorem sphere_simplyConnected : SimplyConnectedSpace UnitTwoSphere :=
  Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)

/-- A nonempty open interval times the surgery two-sphere is simply
connected (MT Proposition 15.3, pp. 357-358). -/
theorem sphere_prod_interval_simplyConnected (a b : ℝ) (hab : a < b) :
    SimplyConnectedSpace (UnitTwoSphere × Ioo a b) := by
  let : SimplyConnectedSpace UnitTwoSphere := sphere_simplyConnected
  let : ContractibleSpace (Ioo a b) := (convex_Ioo a b).contractibleSpace (nonempty_Ioo.mpr hab)
  exact simplyConnectedSpace_prod_contractible _ _

/-- The spherical collar parameter domain is simply connected
(MT Proposition 15.3, pp. 357-358). -/
theorem cylinder_interval_simplyConnected (a b : ℝ) (hab : a < b) :
    IsSimplyConnected (univ ×ˢ Ioo a b : Set RoundCylinderSpace) := by
  let : SimplyConnectedSpace (UnitTwoSphere × Ioo a b) :=
    sphere_prod_interval_simplyConnected a b hab
  exact ((Homeomorph.Set.prod (univ : Set UnitTwoSphere) (Ioo a b)).trans
    ((Homeomorph.Set.univ UnitTwoSphere).prodCongr
      (Homeomorph.refl _))).toHomotopyEquiv.simplyConnectedSpace

/-- The coordinate annulus outside the removed unit ball, inside its
radius-two chart (MT Proposition 15.3, pp. 357-358). -/
def annulus : Set StandardCapSpace := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}

set_option backward.isDefEq.respectTransparency false in
/-- Polar coordinates on the annulus, using Mathlib's radial homeomorphism
(Hatcher Proposition 1.26(b), p. 50). -/
noncomputable def annulusHomeomorph : annulus ≃ₜ (UnitTwoSphere × Ioo (1 : ℝ) 2) := by
  let e := homeomorphUnitSphereProd (E := StandardCapSpace)
  have hn (x : annulus) : x.1 ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one x.2.1)
  refine {
    toFun := fun x => ((e ⟨x.1, hn x⟩).1, ⟨(e ⟨x.1, hn x⟩).2.1, by
      simpa only [e, homeomorphUnitSphereProd_apply_snd_coe, mem_Ioo, annulus,
        mem_ofPred_eq] using x.2⟩)
    invFun := fun y => ⟨(e.symm (y.1, ⟨y.2.1, lt_trans zero_lt_one y.2.2.1⟩)).1, ?_⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · change 1 < ‖y.2.1 • y.1.1‖ ∧ ‖y.2.1 • y.1.1‖ < 2
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one y.2.2.1),
      mem_sphere_zero_iff_norm.mp y.1.2, mul_one, mem_Ioo] using y.2.2
  · intro x
    apply Subtype.ext
    change (e.symm (e ⟨x.1, hn x⟩)).1 = x.1
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x.1, hn x⟩)
  · intro y
    have h := e.apply_symm_apply (y.1, ⟨y.2.1, lt_trans zero_lt_one y.2.2.1⟩)
    apply Prod.ext
    · change (e (e.symm (y.1, ⟨y.2.1, _⟩))).1 = y.1
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun z => z.2.1) h
  · exact (e.continuous.comp (continuous_subtype_val.subtype_mk hn)).fst.prodMk
      ((continuous_subtype_val.comp
        (e.continuous.comp (continuous_subtype_val.subtype_mk hn)).snd).subtype_mk _)
  · exact (continuous_subtype_val.comp (e.symm.continuous.comp
      (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))).subtype_mk _

/-- The annulus between the two surgery radii is simply connected
(Hatcher Proposition 1.26(b), p. 50). -/
theorem annulus_simplyConnected : IsSimplyConnected annulus := by
  let : SimplyConnectedSpace (UnitTwoSphere × Ioo (1 : ℝ) 2) :=
    sphere_prod_interval_simplyConnected 1 2 (by norm_num)
  exact annulusHomeomorph.toHomotopyEquiv.simplyConnectedSpace

end SurgeryCoordinates

namespace SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

/-- The full open chart of the embedded surgery ball
(MT Proposition 15.3, pp. 357-358). -/
def chartRegion : Set A.carrier := B.map '' ball 0 2

/-- The supplied ball coordinates are a subspace homeomorphism
(MT Proposition 15.3, pp. 357-358). -/
def chartHomeomorph : ball (0 : StandardCapSpace) 2 ≃ₜ B.chartRegion :=
  Homeomorph.ofSetInverse B.map B.inverse _ _ B.map_smooth.continuousOn
    B.inverse_smooth.continuousOn (fun _ hx => mem_image_of_mem _ hx)
    (by rintro _ ⟨x, hx, rfl⟩; simpa only [B.left_inverse hx] using hx)
    B.left_inverse B.right_inverse

/-- The surgery chart is open by its supplied open embedding
(MT Proposition 15.3, pp. 357-358). -/
theorem chartRegion_open : IsOpen B.chartRegion := by
  have hrange : range (fun x : ball (0 : StandardCapSpace) 2 => B.map x.1) = B.chartRegion := by
    ext y
    simp [chartRegion]
  exact hrange ▸ B.open_embedding.isOpen_range

/-- The removed closed ball has compact, hence closed, image
(MT Proposition 15.3, pp. 357-358). -/
theorem closedBall_closed : IsClosed B.closedBall :=
  ((isCompact_closedBall (0 : StandardCapSpace) 1).image_of_continuousOn
    (B.map_smooth.continuousOn.mono (closedBall_subset_ball (by norm_num)))).isClosed

/-- The punctured side and open ball chart cover the original manifold
(Hatcher Proposition 1.26(b), p. 50). -/
theorem complement_union_chart : B.closedBallᶜ ∪ B.chartRegion = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ B.closedBall
  · right
    obtain ⟨y, hy, rfl⟩ := hx
    exact mem_image_of_mem _ (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hy)
  · exact Or.inl hx

/-- On the chart, the complement of the removed ball is precisely the
coordinate annulus (MT Proposition 15.3, pp. 357-358). -/
theorem map_mem_complement_iff {x : StandardCapSpace} (hx : x ∈ ball 0 2) :
    B.map x ∈ B.closedBallᶜ ↔ 1 < ‖x‖ := by
  constructor
  · intro h
    by_contra hn
    exact h ⟨x, mem_closedBall_zero_iff.mpr (le_of_not_gt hn), rfl⟩
  · intro h ⟨y, hy, heq⟩
    have hy2 : y ∈ ball (0 : StandardCapSpace) 2 := closedBall_subset_ball (by norm_num) hy
    have hxy : y = x := B.left_inverse.injOn hy2 hx heq
    subst y
    exact (not_le_of_gt h) (mem_closedBall_zero_iff.mp hy)

/-- A radial point in the annulus survives removal of the closed ball
(MT Proposition 15.3, pp. 357-358). -/
theorem radial_mem_complement (z : UnitTwoSphere) {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) :
    B.map (r • z.1) ∈ B.closedBallᶜ := by
  have hn : ‖r • z.1‖ = r := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hr.1),
      mem_sphere_zero_iff_norm.mp z.2, mul_one]
  apply (B.map_mem_complement_iff (mem_ball_zero_iff.mpr (by simpa only [hn] using hr.2))).mpr
  simpa only [hn] using hr.1

/-- The image of the annulus is the overlap in the ball-filling cover
(Hatcher Proposition 1.26(b), p. 50). -/
theorem annulus_image : B.map '' SurgeryCoordinates.annulus = B.closedBallᶜ ∩ B.chartRegion := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy2 : y ∈ ball (0 : StandardCapSpace) 2 := mem_ball_zero_iff.mpr hy.2
    exact ⟨(B.map_mem_complement_iff hy2).mpr hy.1, mem_image_of_mem _ hy2⟩
  · rintro ⟨h, y, hy, rfl⟩
    exact ⟨y, ⟨(B.map_mem_complement_iff hy).mp h, mem_ball_zero_iff.mp hy⟩, rfl⟩

/-- The punctured-chart overlap is simply connected, by polar
coordinates (Hatcher Proposition 1.26(b), p. 50). -/
theorem overlap_simplyConnected : IsSimplyConnected (B.closedBallᶜ ∩ B.chartRegion) := by
  let e : SurgeryCoordinates.annulus ≃ₜ (B.closedBallᶜ ∩ B.chartRegion : Set A.carrier) :=
    Homeomorph.ofSetInverse B.map B.inverse _ _
      (B.map_smooth.continuousOn.mono (fun x hx => mem_ball_zero_iff.mpr hx.2))
      (B.inverse_smooth.continuousOn.mono inter_subset_right)
      (fun x hx => B.annulus_image ▸ mem_image_of_mem _ hx)
      (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := B.annulus_image.symm ▸ hy
        simpa only [B.left_inverse (mem_ball_zero_iff.mpr hx.2)] using hx)
      (fun x hx => B.left_inverse (mem_ball_zero_iff.mpr hx.2))
      (fun y hy => B.right_inverse hy.2)
  let : SimplyConnectedSpace SurgeryCoordinates.annulus :=
    SurgeryCoordinates.annulus_simplyConnected
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- The open ball chart is simply connected (Hatcher Proposition 1.26(b),
p. 50). -/
theorem chart_simplyConnected : IsSimplyConnected B.chartRegion := by
  let : ContractibleSpace (ball (0 : StandardCapSpace) 2) :=
    (convex_ball (0 : StandardCapSpace) 2).contractibleSpace (nonempty_ball.mpr (by norm_num))
  exact B.chartHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

end SurgeryBallEmbedding

end PoincareMT
