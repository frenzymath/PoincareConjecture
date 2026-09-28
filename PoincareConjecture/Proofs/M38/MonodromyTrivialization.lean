import PoincareConjecture.Proofs.M38.MonodromyNormalization

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)

noncomputable def monodromyLocalCoordinates (b0 : UnitCircle)
    (q : MonodromyQuotient phi) : UnitTwoSphere × UnitCircle :=
  (capUnitDirection (monodromyNormalize phi
    (circleAngleLift b0 (monodromyProjection phi q)) q).val, monodromyProjection phi q)

noncomputable def monodromyLocalInverse (b0 : UnitCircle)
    (p : UnitTwoSphere × UnitCircle) : MonodromyQuotient phi :=
  mq (monodromyPolarPoint (p.1, circleAngleLift b0 p.2))

theorem monodromyLocalInverse_projection (b0 : UnitCircle)
    (p : UnitTwoSphere × UnitCircle) :
    monodromyProjection phi (monodromyLocalInverse phi b0 p) = p.2 := by
  rw [monodromyLocalInverse, monodromyProjection_mk, monodromyPolarPoint_logRadius]
  exact circleAngleLift_spec b0 p.2

theorem monodromyLocalCoordinates_left_inv (b0 : UnitCircle)
    (q : MonodromyQuotient phi) :
    monodromyLocalInverse phi b0 (monodromyLocalCoordinates phi b0 q) = q := by
  let s := circleAngleLift b0 (monodromyProjection phi q)
  let x := monodromyNormalize phi s q
  have hx : monodromyLogRadius x = s :=
    monodromyNormalize_logRadius phi s q (circleAngleLift_spec b0 _).symm
  change mq (monodromyPolarPoint (capUnitDirection x.val, s)) = q
  rw [← hx, monodromyPolarPoint_reconstruct]
  exact monodromyNormalize_quotient phi s q

theorem monodromyLocalCoordinates_right_inv (b0 : UnitCircle)
    (p : UnitTwoSphere × UnitCircle) :
    monodromyLocalCoordinates phi b0 (monodromyLocalInverse phi b0 p) = p := by
  apply Prod.ext
  · change capUnitDirection (monodromyNormalize phi
      (circleAngleLift b0 (monodromyProjection phi (monodromyLocalInverse phi b0 p)))
      (monodromyLocalInverse phi b0 p)).val = p.1
    rw [monodromyLocalInverse_projection]
    have hx : monodromyNormalize phi (circleAngleLift b0 p.2)
        (monodromyLocalInverse phi b0 p) =
          monodromyPolarPoint (p.1, circleAngleLift b0 p.2) :=
      monodromyNormalize_eq phi rfl (monodromyPolarPoint_logRadius _)
    rw [hx, monodromyPolarPoint_direction]
  · exact monodromyLocalInverse_projection phi b0 p

theorem monodromyLocalCoordinates_image (b0 : UnitCircle) :
    monodromyLocalCoordinates phi b0 ''
      (monodromyProjection phi ⁻¹' circleLiftArc b0) = Set.univ ×ˢ circleLiftArc b0 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Set.mem_univ _, hq⟩
  · intro hp
    refine ⟨monodromyLocalInverse phi b0 p, ?_,
      monodromyLocalCoordinates_right_inv phi b0 p⟩
    change monodromyProjection phi (monodromyLocalInverse phi b0 p) ∈ circleLiftArc b0
    rw [monodromyLocalInverse_projection]
    exact hp.2

theorem monodromyLocalCoordinates_smooth (b0 : UnitCircle) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ (monodromyLocalCoordinates phi b0)
      (monodromyProjection phi ⁻¹' circleLiftArc b0) := by
  have hs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q => circleAngleLift b0 (monodromyProjection phi q))
      (monodromyProjection phi ⁻¹' circleLiftArc b0) :=
    (circleAngleLift_smooth b0).comp (monodromyProjection_smooth phi).contMDiffOn
      (fun _ hq => hq)
  have hn := monodromyNormalize_smooth phi
    ((circleLiftArc_open b0).preimage (monodromyProjection_continuous phi)) hs
    (fun q _ => (circleAngleLift_spec b0 (monodromyProjection phi q)).symm)
  have hd : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun x : monodromyPunctureOpen => capUnitDirection x.val) :=
    capUnitDirection_smooth.comp_contMDiff contMDiff_subtype_val (fun x => x.property)
  exact (hd.comp_contMDiffOn hn).prodMk (monodromyProjection_smooth phi).contMDiffOn

theorem monodromyLocalInverse_smooth (b0 : UnitCircle) :
    ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ (monodromyLocalInverse phi b0)
      (Set.univ ×ˢ circleLiftArc b0) := by
  have hs : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : UnitTwoSphere × UnitCircle => circleAngleLift b0 p.2)
      (Set.univ ×ˢ circleLiftArc b0) :=
    (circleAngleLift_smooth b0).comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2)
  exact (monodromy_quotient_contMDiff phi).comp_contMDiffOn
    (monodromyPolarPoint_smooth.comp_contMDiffOn (contMDiff_fst.contMDiffOn.prodMk hs))

theorem monodromy_local_trivialization (b : UnitCircle) :
    ∃ U : Set UnitCircle, IsOpen U ∧ b ∈ U ∧
      ∃ f : MonodromyQuotient phi → UnitTwoSphere × UnitCircle,
      ∃ g : UnitTwoSphere × UnitCircle → MonodromyQuotient phi,
        f '' (monodromyProjection phi ⁻¹' U) = Set.univ ×ˢ U ∧
        Set.LeftInvOn g f (monodromyProjection phi ⁻¹' U) ∧
        Set.LeftInvOn f g (Set.univ ×ˢ U) ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ f (monodromyProjection phi ⁻¹' U) ∧
        ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ g (Set.univ ×ˢ U) ∧
        ∀ x ∈ monodromyProjection phi ⁻¹' U, (f x).2 = monodromyProjection phi x := by
  exact ⟨circleLiftArc b, circleLiftArc_open b, circleLiftArc_self b,
    monodromyLocalCoordinates phi b, monodromyLocalInverse phi b,
    monodromyLocalCoordinates_image phi b,
    fun q _ => monodromyLocalCoordinates_left_inv phi b q,
    fun p _ => monodromyLocalCoordinates_right_inv phi b p,
    monodromyLocalCoordinates_smooth phi b, monodromyLocalInverse_smooth phi b,
    fun _ _ => rfl⟩

end PoincareConjecture.M38
