import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTriangleReconstruction

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

variable [FiniteDimensional ℝ E]

def sideGlueRelation (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop)
    (x y : carrier K label) : Prop :=
  ∃ s t : Triangle K,
    x.1 ∈ copy K label s ∧ y.1 ∈ copy K label t ∧
      Relation.EqvGen contact s t ∧ x.1.1 = y.1.1

theorem sideGlueRelation_refl (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) (x : carrier K label) :
    sideGlueRelation K label contact x x := by
  obtain ⟨s, hs⟩ := mem_iUnion.mp x.2
  exact ⟨s, s, hs, hs, Relation.EqvGen.refl s, rfl⟩

theorem sideGlueRelation_symm (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) {x y : carrier K label}
    (hxy : sideGlueRelation K label contact x y) :
    sideGlueRelation K label contact y x := by
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hxy
  exact ⟨t, s, ht, hs, hst.symm, hxy.symm⟩

theorem sideGlueRelation_trans (label : Triangle K → ℝ)
    (hi : Function.Injective label)
    (contact : Triangle K → Triangle K → Prop)
    {x y z : carrier K label}
    (hxy : sideGlueRelation K label contact x y)
    (hyz : sideGlueRelation K label contact y z) :
    sideGlueRelation K label contact x z := by
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hxy
  obtain ⟨u, v, hu, hv, huv, hyz⟩ := hyz
  have htu : t = u := by
    apply hi
    exact ((mem_copy_iff K label t y.1).mp ht).2.symm.trans
      ((mem_copy_iff K label u y.1).mp hu).2
  subst u
  exact ⟨s, v, hs, hv, @Relation.EqvGen.trans _ contact s t v hst huv, hxy.trans hyz⟩

def sideGlueSetoid (label : Triangle K → ℝ)
    (hi : Function.Injective label)
    (contact : Triangle K → Triangle K → Prop) :
    Setoid (carrier K label) :=
  { r := sideGlueRelation K label contact
    iseqv := ⟨sideGlueRelation_refl K label contact,
      sideGlueRelation_symm K label contact,
      sideGlueRelation_trans K label hi contact⟩ }

theorem sideGlueRelation_fiber (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label}
    (hxy : sideGlueRelation K label contact x y) :
    x.1.1 = y.1.1 := by
  rcases hxy with ⟨s, t, hs, ht, hst, hxy⟩
  exact hxy

private def sideGluePairSet (label : Triangle K → ℝ)
    (s t : Triangle K) :
    Set ((carrier K label) × (carrier K label)) :=
  {q | q.1.1 ∈ copy K label s ∧
      q.2.1 ∈ copy K label t ∧ q.1.1.1 = q.2.1.1}

private theorem isClosed_sideGluePairSet (label : Triangle K → ℝ)
    (s t : Triangle K) :
    IsClosed (sideGluePairSet K label s t) := by
  have hcopy (s : Triangle K) : IsClosed (copy K label s) := by
    exact (s.val.finite_toSet.isCompact_convexHull ℝ |>.image
      (inclusion (E := E) (label s)).continuous).isClosed
  have hleft : IsClosed {q : (carrier K label) × (carrier K label) |
      q.1.1 ∈ copy K label s} :=
    (hcopy s).preimage (continuous_subtype_val.comp continuous_fst)
  have hright : IsClosed {q : (carrier K label) × (carrier K label) |
      q.2.1 ∈ copy K label t} :=
    (hcopy t).preimage (continuous_subtype_val.comp continuous_snd)
  have heq : IsClosed {q : (carrier K label) × (carrier K label) |
      q.1.1.1 = q.2.1.1} := by
    apply isClosed_eq
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  exact hleft.inter (hright.inter heq)

theorem isClosed_sideGlueRelation (hK : K.faces.Finite)
    (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) :
    IsClosed {q : (carrier K label) × (carrier K label) |
      sideGlueRelation K label contact q.1 q.2} := by
  classical
  letI : Finite (Triangle K) :=
    (hK.subset (fun _ h ↦ h.1)).to_subtype
  letI : Fintype (Triangle K) := Fintype.ofFinite _
  let Pair := {p : Triangle K × Triangle K //
    Relation.EqvGen contact p.1 p.2}
  letI : Fintype Pair := Fintype.ofFinite _
  have hEq : {q : (carrier K label) × (carrier K label) |
      sideGlueRelation K label contact q.1 q.2} =
      ⋃ p : Pair, sideGluePairSet K label p.1.1 p.1.2 := by
    ext q
    constructor
    · rintro ⟨s, t, hs, ht, hst, heq⟩
      let p : Pair := ⟨(s, t), hst⟩
      refine mem_iUnion.mpr ⟨p, ?_⟩
      exact ⟨hs, ht, heq⟩
    · intro hq
      obtain ⟨p, hp⟩ := mem_iUnion.mp hq
      exact ⟨p.1.1, p.1.2, hp.1, hp.2.1, p.2, hp.2.2⟩
  rw [hEq]
  apply isClosed_iUnion_of_finite
  intro p
  apply isClosed_sideGluePairSet K label p.1.1 p.1.2

end PoincareConjecture.M76.OriginalTriangleCopies
