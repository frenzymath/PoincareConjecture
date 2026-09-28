import PoincareConjecture.Proofs.M38.SpherePunctureCoordinates
import PoincareConjecture.Proofs.M38.TwoBallAffineNormalization
import PoincareConjecture.Proofs.M38.StereographicOpposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem threeSphereStereo_opposite_center (a : UnitThreeSphere) :
    stereographic' 3 (-a) a = 0 := by
  change threeSphereStereoFrame (-a)
    (stereographic (norm_eq_of_mem_sphere (-a)) a) = 0
  rw [stereographic_neg_apply, map_zero]

theorem threeSphereStereoInverse_opposite_zero (a : UnitThreeSphere) :
    threeSphereStereoInverse (-a) 0 = a := by
  rw [← threeSphereStereo_opposite_center a]
  exact (stereographic' 3 (-a)).left_inv (by
    simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ a)

noncomputable def spherePoleReferenceBall (p : sphereCarrier.{u}.carrier) :
    SurgeryBallEmbedding sphereCarrier.{u} := by
  let f : StandardCapSpace → sphereCarrier.{u}.carrier :=
    fun x => ULift.up (threeSphereStereoInverse (-p.down) x)
  let g : sphereCarrier.{u}.carrier → StandardCapSpace :=
    fun y => stereographic' 3 (-p.down) y.down
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (threeManifold_up_contMDiff UnitThreeSphere).comp
      (threeSphereStereoLocalDiffeomorph (-p.down)).contMDiff
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) := by
    apply (threeSphereStereo_smooth (-p.down)).comp
      (threeManifold_down_contMDiff UnitThreeSphere).contMDiffOn
    rintro _ ⟨x, _, rfl⟩
    change threeSphereStereoInverse (-p.down) x ≠ -p.down
    intro heq
    exact spherePunctureInverse_ne
      (ULift.up (-p.down) : sphereCarrier.{u}.carrier)
      (ULift.up x : euclideanCarrier.{u}.carrier) (ULift.ext _ _ heq)
  have hleft : Set.LeftInvOn g f (Metric.ball (0 : StandardCapSpace) 2) := by
    intro x _
    exact (stereographic' 3 (-p.down)).right_inv (by simp)
  exact {
    map := f
    inverse := g
    map_smooth := hf.contMDiffOn
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball
      hf.contMDiffOn hg hleft }

theorem spherePoleReferenceBall_map (p : sphereCarrier.{u}.carrier)
    (x : StandardCapSpace) :
    (spherePoleReferenceBall p).map x =
      ULift.up (threeSphereStereoInverse (-p.down) x) := rfl

theorem spherePoleReferenceBall_inverse (p y : sphereCarrier.{u}.carrier) :
    (spherePoleReferenceBall p).inverse y = stereographic' 3 (-p.down) y.down := rfl

theorem spherePoleReferenceBall_center (p : sphereCarrier.{u}.carrier) :
    (spherePoleReferenceBall p).map 0 = p := by
  apply ULift.ext
  exact threeSphereStereoInverse_opposite_zero p.down

theorem exists_sphereBallPoleNormalization
    (B : SurgeryBallEmbedding sphereCarrier.{u}) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
      sphereCarrier.{u}.carrier sphereCarrier.{u}.carrier ∞,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b : ℝ,
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => stereographic' 3 (-(B.map 0).down) (B.map x).down) 0 ∧
      0 < b ∧ b < 1 ∧ e (B.map 0) = B.map 0 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        e (B.map x) = ULift.up
          (threeSphereStereoInverse (-(B.map 0).down) (L (b • x)))) ∧
      (∀ y : sphereCarrier.{u}.carrier,
        y ∉ B.map '' Metric.closedBall 0 (3 / 2) → e y = y) := by
  let C := spherePoleReferenceBall (B.map 0)
  have hcenter : C.map 0 = B.map 0 := spherePoleReferenceBall_center _
  have hBC : B.map 0 ∈ C.map '' Metric.ball (0 : StandardCapSpace) 2 :=
    ⟨0, by simp, hcenter⟩
  have hzero : C.inverse (B.map 0) = 0 := threeSphereStereo_opposite_center _
  obtain ⟨e, L, b, hL, hb, hb1, hinner, _, hfix⟩ :=
    exists_surgeryBallAffineNormalizationCompact B C hBC
  have hformula (x : StandardCapSpace) (hx : ‖x‖ ≤ 5 / 4) :
      e (B.map x) = ULift.up
        (threeSphereStereoInverse (-(B.map 0).down) (L (b • x))) := by
    simpa only [hzero, zero_add, C, spherePoleReferenceBall_map] using hinner x hx
  refine ⟨e, L, b, hL, hb, hb1, ?_, hformula, hfix⟩
  rw [hformula 0 (by norm_num), smul_zero, map_zero,
    threeSphereStereoInverse_opposite_zero]
  rfl

theorem sphereBallPoleNormalization_fixes_disjoint
    (B D : SurgeryBallEmbedding sphereCarrier.{u})
    (hBD : Disjoint (B.map '' Metric.ball 0 2) (D.map '' Metric.ball 0 2))
    (e : Diffeomorph (𝓡 3) (𝓡 3)
      sphereCarrier.{u}.carrier sphereCarrier.{u}.carrier ∞)
    (hfix : ∀ y : sphereCarrier.{u}.carrier,
      y ∉ B.map '' Metric.closedBall 0 (3 / 2) → e y = y)
    (x : StandardCapSpace) (hx : x ∈ Metric.ball 0 2) : e (D.map x) = D.map x := by
  apply hfix
  intro hy
  exact Set.disjoint_left.mp hBD
    ((Set.image_mono (Metric.closedBall_subset_ball (by norm_num))) hy) ⟨x, hx, rfl⟩

end PoincareConjecture.M38
