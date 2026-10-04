import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CoreProjectionAlgebra
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.CoreRegionBoundary

/-!
# Rational core projections are the geometric box bases

Region membership supplies positive residual mass. The rational
projection therefore agrees with the core base in the product
homeomorphism, preserves simplex coordinates, and is smooth near
every region point. See Cairns 1940, pp. 803--805, and M76
derivation 45.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Residual mass on a face is the product of its core-size
factor and the box radial factor.
See Cairns p. 803 and M76 derivation 45. -/
theorem residualMass_eq_boxScale_mul (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    residualMass s η q.val = boxScale s η (fun j : {i // i ∉ s} => q.val j) *
      (1 - (Fintype.card s : ℝ) * η) := by
  have hsum : (∑ i : s, q.val i) + ∑ j : {i // i ∉ s}, q.val j = 1 :=
    ((faceRegionBoxHomeomorph s hη) q).property.2.2
  have hm : residualMass s η q.val = (∑ i : s, q.val i) - (Fintype.card s : ℝ) * η := by
    simp only [residualMass, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_coe_sort, Fintype.card_coe]
  rw [hm, boxScale_mul (sub_pos.mpr (face_threshold_bound s hη hbound)).ne']
  linarith

omit [DecidableEq ι] in
/-- A region point has strictly positive face residual mass,
including all its boundary attachments.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem residualMass_pos_of_mem_faceRegion (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    0 < residualMass s η q.val := by
  classical
  have hc : (Fintype.card s : ℝ) + Fintype.card {i // i ∉ s} = Fintype.card ι := by
    simpa using Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) (fun _ => (1 : ℝ))
  have ha := boxScale_pos (ι := s) hη (hc ▸ hbound)
    ((faceRegionBoxHomeomorph s hη) q).property.2.1
  rw [residualMass_eq_boxScale_mul s hη hbound q]
  exact mul_pos ha (sub_pos.mpr (face_threshold_bound s hη hbound))

/-- The rational projection restricted to its face is exactly
the geometric core base from the product homeomorphism.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem projectToFace_eq_boxBase (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    (fun i : s => projectToFace s η q.val i) =
      (((faceRegionProductHomeomorph s hη hbound).symm q).1 : s → ℝ) := by
  have hden : 1 - (s.card : ℝ) * η ≠ 0 := by
    simpa only [Fintype.card_coe] using (sub_pos.mpr (face_threshold_bound s hη hbound)).ne'
  funext i
  simp only [projectToFace, if_pos i.property]
  change η + (q.val i - η) * (1 - (s.card : ℝ) * η) / residualMass s η q.val =
    η + (q.val i - η) / boxScale s η (fun j : {i // i ∉ s} => q.val j)
  rw [residualMass_eq_boxScale_mul s hη hbound q, Fintype.card_coe,
    mul_div_mul_right _ _ hden]

/-- The projection of a region point lies in the actual closed
face core in barycentric coordinates.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem projectToFace_mem_core (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    (fun i : s => projectToFace s η q.val i) ∈ stdSimplexCore s η := by
  rw [projectToFace_eq_boxBase s hη hbound q]
  exact ((faceRegionProductHomeomorph s hη hbound).symm q).1.property

/-- The core projection remains in the original full simplex.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem projectToFace_mem_stdSimplex (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    projectToFace s η q.val ∈ stdSimplex ℝ ι := by
  have hcore := projectToFace_mem_core s hη hbound q
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i ∈ s
    · exact hη.trans (hcore.1 ⟨i, hi⟩)
    · simp only [projectToFace, if_neg hi, le_refl]
  · have hsum : (∑ i, projectToFace s η q.val i) = ∑ i ∈ s, projectToFace s η q.val i := by
      symm
      apply Fintype.sum_subset
      intro i hi
      by_contra his
      exact hi (by simp only [projectToFace, if_neg his])
    rw [hsum]
    exact sum_projectToFace s η q.val (residualMass_pos_of_mem_faceRegion s hη hbound q).ne'

/-- The rational core projection is smooth wherever its
residual mass is nonzero. See Cairns pp. 804--805 and M76 derivation 45. -/
theorem contDiffAt_projectToFace (s : Finset ι) (η : ℝ) (n : ℕ∞ω) (q : ι → ℝ)
    (hq : residualMass s η q ≠ 0) : ContDiffAt ℝ n (projectToFace s η) q := by
  have hm : ContDiff ℝ n (residualMass s η) := by
    unfold residualMass
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i ∈ s
  · simp only [projectToFace, if_pos hi]
    exact contDiffAt_const.add
      ((((contDiff_apply ℝ ℝ i).contDiffAt.sub contDiffAt_const).mul contDiffAt_const).div
        hm.contDiffAt hq)
  · simpa only [projectToFace, if_neg hi] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : ι → ℝ => (0 : ℝ)) q)

end StdSimplexCore
