import PoincareLib.Topology.Manifold.Surgery.Event.Tube.TubeExclusion
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Punctured projective three-space

The literal antipodal quotient is Hausdorff. Stereographic projection proves
that removing an antipodal pair from the three-sphere leaves a connected
space. Its quotient is punctured projective space, which is connected and
noncompact. These elementary facts exclude whole compact cap components.
-/

set_option autoImplicit false

open Set Topology Metric

namespace PoincareMT.M38

/-- Saturating a set under the actual antipodal quotient adds its antipodes. -/
theorem projective_quotient_saturation (U : Set UnitThreeSphere) :
    (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹'
      ((Quotient.mk' : UnitThreeSphere → RealProjectiveThree) '' U) =
        U ∪ (Neg.neg ⁻¹' U) := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    rcases (Quotient.exact heq : y = x ∨ y = -x) with rfl | rfl
    · exact Or.inl hy
    · exact Or.inr hy
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨-x, hx, Quotient.sound (Or.inr rfl)⟩

/-- The antipodal projection is open for the literal quotient topology. -/
theorem projective_open_quotient :
    IsOpenQuotientMap (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) := by
  refine ⟨Quotient.mk_surjective, continuous_quotient_mk', ?_⟩
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  rw [projective_quotient_saturation]
  exact hU.union (hU.preimage continuous_neg)

/-- Closedness of the diagonal and antipodal graph makes this quotient Hausdorff. -/
theorem projective_t2 : T2Space RealProjectiveThree := by
  apply (t2Space_iff_of_isOpenQuotientMap projective_open_quotient).mpr
  have heq : {z : UnitThreeSphere × UnitThreeSphere |
      (Quotient.mk' z.1 : RealProjectiveThree) = Quotient.mk' z.2} =
      {z | z.1 = z.2} ∪ {z | z.1 = -z.2} := by
    ext z
    exact Quotient.eq
  rw [heq]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst (continuous_neg.comp continuous_snd))

/-- A unit vector is different from its antipode. -/
theorem three_sphere_neg_ne (a : UnitThreeSphere) : -a ≠ a := by
  intro h
  have ha : (a : EuclideanSpace ℝ (Fin 4)) = 0 := by
    ext i
    have hi := congrArg (fun z : UnitThreeSphere => (z : EuclideanSpace ℝ (Fin 4)) i) h
    change -(a.val i) = a.val i at hi
    change a.val i = 0
    linarith
  exact ne_zero_of_mem_unit_sphere a ha

/-- Stereographic projection identifies the sphere without an antipodal pair
with Euclidean three-space without one point, so it is connected and nonempty. -/
theorem three_sphere_antipodal_compl_connected (a : UnitThreeSphere) :
    IsConnected {x : UnitThreeSphere | x ≠ a ∧ x ≠ -a} := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let e := stereographic' 3 a
  have hneg : -a ∈ e.source := by
    simpa only [e, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff]
      using three_sphere_neg_ne a
  have hsource (x : UnitThreeSphere) (hx : x ≠ a) : x ∈ e.source := by
    simpa only [e, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have htarget (z : EuclideanSpace ℝ (Fin 3)) : z ∈ e.target := by
    simp only [e, stereographic'_target, Set.mem_univ]
  have hcont : Continuous e.symm := by
    apply continuousOn_univ.mp
    simpa only [OpenPartialHomeomorph.symm_source, e, stereographic'_target]
      using e.symm.continuousOn
  have himage : e.symm '' ({e (-a)}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) =
      {x : UnitThreeSphere | x ≠ a ∧ x ≠ -a} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzsource := e.map_target (htarget z)
      refine ⟨?_, ?_⟩
      · simpa only [e, stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff]
          using hzsource
      · intro heq
        exact hz ((e.right_inv (htarget z)).symm.trans (congrArg e heq))
    · intro hx
      refine ⟨e x, ?_, e.left_inv (hsource x hx.1)⟩
      intro heq
      exact hx.2 (e.injOn (hsource x hx.1) hneg heq)
  rw [← himage]
  exact (isConnected_compl_singleton_of_one_lt_rank
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) (e (-a))).image e.symm hcont.continuousOn

/-- The inverse image of a projective puncture is the complement of its two lifts. -/
theorem projective_puncture_preimage (a : UnitThreeSphere) :
    (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹'
      {q | q ≠ Quotient.mk' a} = {x | x ≠ a ∧ x ≠ -a} := by
  ext x
  change (¬ (Quotient.mk' x : RealProjectiveThree) = Quotient.mk' a) ↔ _
  constructor
  · intro h
    exact ⟨fun hx => h (congrArg Quotient.mk' hx),
      fun hx => h (Quotient.sound (Or.inr hx))⟩
  · rintro ⟨h₁, h₂⟩ h
    exact (Quotient.exact h : x = a ∨ x = -a).elim h₁ h₂

/-- The actual punctured projective carrier is the connected image of the
three-sphere without the two lifts of its puncture. -/
theorem punctured_projective_connected (p : RealProjectiveThree) :
    IsConnected {q : RealProjectiveThree | q ≠ p} := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective p
  have hpre : IsConnected
      ((Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹'
        {q | q ≠ Quotient.mk' a}) := by
    rw [projective_puncture_preimage]
    exact three_sphere_antipodal_compl_connected a
  have himage := hpre.image (Quotient.mk' : UnitThreeSphere → RealProjectiveThree)
    continuous_quotient_mk'.continuousOn
  rw [Set.image_preimage_eq _ projective_open_quotient.surjective] at himage
  exact himage

/-- Compactness of the punctured projective carrier would make its lifted
antipodal complement both open and closed in the connected three-sphere. -/
theorem punctured_projective_not_compact (p : RealProjectiveThree) :
    ¬ IsCompact {q : RealProjectiveThree | q ≠ p} := by
  let : T2Space RealProjectiveThree := projective_t2
  let : ConnectedSpace UnitThreeSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective p
  intro hcompact
  have hclosed : IsClosed {x : UnitThreeSphere | x ≠ a ∧ x ≠ -a} := by
    rw [← projective_puncture_preimage]
    exact hcompact.isClosed.preimage continuous_quotient_mk'
  have hopen : IsOpen {x : UnitThreeSphere | x ≠ a ∧ x ≠ -a} :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun continuous_id continuous_const)
  have heq := (IsClopen.eq_univ ⟨hclosed, hopen⟩
    (three_sphere_antipodal_compl_connected a).nonempty)
  have ha : a ∈ {x : UnitThreeSphere | x ≠ a ∧ x ≠ -a} :=
    heq.symm ▸ Set.mem_univ a
  exact ha.1 rfl

end PoincareMT.M38
