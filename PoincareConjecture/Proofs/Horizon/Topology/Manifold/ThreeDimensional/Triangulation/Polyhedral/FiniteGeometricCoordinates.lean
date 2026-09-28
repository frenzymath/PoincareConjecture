import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.FiniteOrderComplex
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open scoped BigOperators

universe u

namespace Poincare.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

noncomputable local instance (K : Geometry.SimplicialComplex Real E) :
    DecidableEq (K.vertices → Real) := fun _ _ => Classical.propDecidable _

theorem simplicialComplex_convex_weights_unique
    (K : Geometry.SimplicialComplex Real E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (w w' : E → Real)
    (hw : ∀ v ∈ s, 0 ≤ w v) (hw' : ∀ v ∈ t, 0 ≤ w' v)
    (hwsum : ∑ v ∈ s, w v = 1) (hw'sum : ∑ v ∈ t, w' v = 1)
    (hwzero : ∀ v, v ∉ s → w v = 0) (hw'zero : ∀ v, v ∉ t → w' v = 0)
    (heq : (∑ v ∈ s, w v • v) = ∑ v ∈ t, w' v • v) : w = w' := by
  classical
  let x := ∑ v ∈ s, w v • v
  have hxs : x ∈ convexHull Real (s : Set E) :=
    Finset.mem_convexHull'.mpr ⟨w, hw, hwsum, rfl⟩
  have hxt : x ∈ convexHull Real (t : Set E) :=
    Finset.mem_convexHull'.mpr ⟨w', hw', hw'sum, heq.symm⟩
  have hxi : x ∈ convexHull Real ((s ∩ t : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hxs, hxt⟩
  obtain ⟨u, _, husum, hux⟩ := Finset.mem_convexHull'.mp hxi
  let z : E → Real := fun v => if v ∈ s ∩ t then u v else 0
  have hzsum (a : Finset E) (ha : s ∩ t ⊆ a) : ∑ v ∈ a, z v = 1 := by
    calc
      ∑ v ∈ a, z v = ∑ v ∈ s ∩ t, z v := by
        apply (Finset.sum_subset ha _).symm
        intro v _ hv
        simp only [z, if_neg hv]
      _ = ∑ v ∈ s ∩ t, u v := Finset.sum_congr rfl
        (fun v hv => by simp only [z, if_pos hv])
      _ = 1 := husum
  have hzval (a : Finset E) (ha : s ∩ t ⊆ a) : (∑ v ∈ a, z v • v) = x := by
    calc
      ∑ v ∈ a, z v • v = ∑ v ∈ s ∩ t, z v • v := by
        apply (Finset.sum_subset ha _).symm
        intro v _ hv
        simp only [z, if_neg hv, zero_smul]
      _ = ∑ v ∈ s ∩ t, u v • v := Finset.sum_congr rfl
        (fun v hv => by simp only [z, if_pos hv])
      _ = x := hux
  have hsz : ∀ v ∈ s, w v = z v :=
    (K.indep hs).eq_of_sum_eq_sum_subtype
      (hwsum.trans (hzsum s Finset.inter_subset_left).symm)
      (hzval s Finset.inter_subset_left).symm
  have htz : ∀ v ∈ t, w' v = z v :=
    (K.indep ht).eq_of_sum_eq_sum_subtype
      (hw'sum.trans (hzsum t Finset.inter_subset_right).symm)
      (heq.symm.trans (hzval t Finset.inter_subset_right).symm)
  funext v
  have hzoff (a : Finset E) (ha : s ∩ t ⊆ a) (hv : v ∉ a) : z v = 0 := by
    simp only [z, if_neg (fun h => hv (ha h))]
  have hvw : w v = z v := by
    by_cases hv : v ∈ s
    · exact hsz v hv
    · exact (hwzero v hv).trans (hzoff s Finset.inter_subset_left hv).symm
  have hvw' : w' v = z v := by
    by_cases hv : v ∈ t
    · exact htz v hv
    · exact (hw'zero v hv).trans (hzoff t Finset.inter_subset_right hv).symm
  exact hvw.trans hvw'.symm

theorem finite_simplicialComplex_vertices
    (K : Geometry.SimplicialComplex Real E) (hK : K.faces.Finite) : K.vertices.Finite := by
  rw [K.vertices_eq]
  exact hK.biUnion (fun s _ => s.finite_toSet)

noncomputable def finiteGeometricCoordinates (K : Geometry.SimplicialComplex Real E) :
    Geometry.SimplicialComplex Real (K.vertices → Real) := by
  classical
  let A : PreAbstractSimplicialComplex K.vertices :=
    { faces := {s | s.image Subtype.val ∈ K.faces}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨Finset.image_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
        intro t hts ht
        exact K.down_closed hs (Finset.image_subset_image hts) (Finset.image_nonempty.mpr ht) }
  refine Geometry.SimplicialComplex.ofAffineIndependent
    (A.map (fun v => Pi.single v (1 : Real))) ?_
  apply (Pi.linearIndependent_single_one K.vertices Real).affineIndependent.range.mono
  intro z hz
  simp only [Set.mem_iUnion, Finset.mem_coe] at hz
  obtain ⟨t, ⟨s, hs, rfl⟩, hz⟩ := hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨v, rfl⟩

open scoped Classical in
theorem finiteGeometricCoordinates_faces
    (K : Geometry.SimplicialComplex Real E) (t : Finset (K.vertices → Real)) :
    t ∈ (finiteGeometricCoordinates K).faces ↔
      ∃ s : Finset K.vertices, s.image Subtype.val ∈ K.faces ∧
        t = s.image (fun v => Pi.single v (1 : Real)) := by
  classical
  change (∃ s : Finset K.vertices, s.image Subtype.val ∈ K.faces ∧
    s.image (fun v => Pi.single v (1 : Real)) = t) ↔ _
  exact ⟨fun ⟨s, hs, hst⟩ => ⟨s, hs, hst.symm⟩,
    fun ⟨s, hs, hts⟩ => ⟨s, hs, hts.symm⟩⟩

theorem finiteGeometricCoordinates_finite
    (K : Geometry.SimplicialComplex Real E) [Finite K.vertices] :
    (finiteGeometricCoordinates K).faces.Finite := by
  classical
  let := Fintype.ofFinite K.vertices
  refine (Set.finite_range (fun s : Finset K.vertices =>
    s.image (fun v => Pi.single v (1 : Real)))).subset ?_
  intro t ht
  obtain ⟨s, hs, rfl⟩ := (finiteGeometricCoordinates_faces K t).mp ht
  exact Set.mem_range_self s

open scoped Classical in
theorem finiteGeometricCoordinates_space
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices]
    (z : K.vertices → Real) :
    z ∈ (finiteGeometricCoordinates K).space ↔
      (∀ v, 0 ≤ z v) ∧ (∑ v, z v) = 1 ∧
        ∃ s : Finset K.vertices, s.image Subtype.val ∈ K.faces ∧
          ∀ v, z v ≠ 0 → v ∈ s := by
  classical
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
    obtain ⟨s, hs, rfl⟩ := (finiteGeometricCoordinates_faces K t).mp ht
    have hsimplex : z ∈ stdSimplex Real K.vertices := by
      apply convexHull_min _ (convex_stdSimplex Real K.vertices) hzt
      intro q hq
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      exact single_mem_stdSimplex Real v
    refine ⟨hsimplex.1, hsimplex.2, s, hs, ?_⟩
    intro v hv
    by_contra hvs
    apply hv
    have hzero : Convex Real {q : K.vertices → Real | q v = 0} := by
      intro a ha b hb c d hc hd hcd
      change c * a v + d * b v = 0
      rw [ha, hb]
      simp
    apply convexHull_min _ hzero hzt
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    have hvw : v ≠ w := fun h => hvs (h ▸ hw)
    simp only [Set.mem_ofPred_eq, Pi.single_apply, if_neg hvw]
  · rintro ⟨hz, hsum, s, hs, hsupport⟩
    have hszero (v : K.vertices) (hv : v ∉ s) : z v = 0 :=
      by_contra fun h => hv (hsupport v h)
    have hsSum : ∑ v ∈ s, z v = 1 := by
      calc
        ∑ v ∈ s, z v = ∑ v, z v :=
          Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => hszero v hv)
        _ = 1 := hsum
    have hvector : ∑ v ∈ s, z v • Pi.single v (1 : Real) = z := by
      funext w
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero]
      by_cases hw : w ∈ s
      · simp [hw]
      · simp [hw, hszero w hw]
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨s.image (fun v => Pi.single v (1 : Real)),
      (finiteGeometricCoordinates_faces K _).mpr ⟨s, hs, rfl⟩, ?_⟩
    rw [← hvector, ← Finset.centerMass_eq_of_sum_1 _ _ hsSum]
    apply Finset.centerMass_mem_convexHull
    · exact fun v _ => hz v
    · rw [hsSum]
      exact zero_lt_one
    · intro v hv
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

noncomputable def geometricVertexWeights
    (K : Geometry.SimplicialComplex Real E) (z : K.vertices → Real) (x : E) : Real := by
  classical
  exact if hx : x ∈ K.vertices then z ⟨x, hx⟩ else 0

theorem geometricVertexWeights_apply
    (K : Geometry.SimplicialComplex Real E) (z : K.vertices → Real) (v : K.vertices) :
    geometricVertexWeights K z v.val = z v := by
  simp only [geometricVertexWeights, dif_pos v.property]

open scoped Classical in
theorem geometricVertexWeights_sum
    (K : Geometry.SimplicialComplex Real E) (z : K.vertices → Real)
    (s : Finset K.vertices) :
    (∑ x ∈ s.image Subtype.val, geometricVertexWeights K z x) = ∑ v ∈ s, z v := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  exact Finset.sum_congr rfl (fun v _ => geometricVertexWeights_apply K z v)

open scoped Classical in
theorem geometricVertexWeights_sum_smul
    (K : Geometry.SimplicialComplex Real E) (z : K.vertices → Real)
    (s : Finset K.vertices) :
    (∑ x ∈ s.image Subtype.val, geometricVertexWeights K z x • x) =
      ∑ v ∈ s, z v • v.val := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  exact Finset.sum_congr rfl (fun v _ => by rw [geometricVertexWeights_apply])

open scoped Classical in
theorem geometricVertexWeights_support
    (K : Geometry.SimplicialComplex Real E) (z : K.vertices → Real)
    (s : Finset K.vertices) (hs : ∀ v, z v ≠ 0 → v ∈ s) :
    ∀ x, x ∉ s.image Subtype.val → geometricVertexWeights K z x = 0 := by
  classical
  intro x hx
  unfold geometricVertexWeights
  split_ifs with hv
  · by_contra hz
    exact hx (Finset.mem_image.mpr ⟨⟨x, hv⟩, hs ⟨x, hv⟩ hz, rfl⟩)
  · rfl

noncomputable def finiteGeometricEvaluation
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices] :
    C((finiteGeometricCoordinates K).space, E) where
  toFun z := ∑ v, z.val v • v.val
  continuous_toFun := continuous_finsetSum _ fun v _ =>
    ((continuous_apply v).comp continuous_subtype_val).smul continuous_const

theorem finiteGeometricEvaluation_injective
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices] :
    Function.Injective (finiteGeometricEvaluation K) := by
  classical
  intro z z' heq
  obtain ⟨hz, hzsum, s, hs, hsz⟩ := (finiteGeometricCoordinates_space K z.val).mp z.property
  obtain ⟨hz', hz'sum, t, ht, htz⟩ := (finiteGeometricCoordinates_space K z'.val).mp z'.property
  have hsum (a : Finset K.vertices) (y : K.vertices → Real)
      (hy : ∀ v, y v ≠ 0 → v ∈ a) : ∑ v ∈ a, y v = ∑ v, y v :=
    Finset.sum_subset (Finset.subset_univ a) (fun v _ hv =>
      by_contra fun hn => hv (hy v hn))
  have hval (a : Finset K.vertices) (y : K.vertices → Real)
      (hy : ∀ v, y v ≠ 0 → v ∈ a) : (∑ v ∈ a, y v • v.val) = ∑ v, y v • v.val := by
    apply Finset.sum_subset (Finset.subset_univ a)
    intro v _ hv
    have hzero : y v = 0 := by_contra fun hn => hv (hy v hn)
    rw [hzero, zero_smul]
  have hweights := simplicialComplex_convex_weights_unique K hs ht
    (geometricVertexWeights K z.val) (geometricVertexWeights K z'.val)
    (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      rw [geometricVertexWeights_apply]
      exact hz v)
    (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      rw [geometricVertexWeights_apply]
      exact hz' v)
    (by rw [geometricVertexWeights_sum, hsum s z.val hsz, hzsum])
    (by rw [geometricVertexWeights_sum, hsum t z'.val htz, hz'sum])
    (geometricVertexWeights_support K z.val s hsz)
    (geometricVertexWeights_support K z'.val t htz)
    (by
      rw [geometricVertexWeights_sum_smul, geometricVertexWeights_sum_smul,
        hval s z.val hsz, hval t z'.val htz]
      exact heq)
  apply Subtype.ext
  funext v
  have h := congrArg (fun w : E → Real => w v.val) hweights
  simpa only [geometricVertexWeights_apply] using h

theorem finiteGeometricEvaluation_mem
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices]
    (z : (finiteGeometricCoordinates K).space) : finiteGeometricEvaluation K z ∈ K.space := by
  classical
  obtain ⟨hz, hsum, s, hs, hsupport⟩ :=
    (finiteGeometricCoordinates_space K z.val).mp z.property
  apply Geometry.SimplicialComplex.mem_space_iff.mpr
  refine ⟨s.image Subtype.val, hs, ?_⟩
  apply Finset.mem_convexHull'.mpr
  refine ⟨geometricVertexWeights K z.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    rw [geometricVertexWeights_apply]
    exact hz v
  · rw [geometricVertexWeights_sum]
    calc
      ∑ v ∈ s, z.val v = ∑ v, z.val v :=
        Finset.sum_subset (Finset.subset_univ s) (fun v _ hv =>
          by_contra fun hn => hv (hsupport v hn))
      _ = 1 := hsum
  · rw [geometricVertexWeights_sum_smul]
    apply Finset.sum_subset (Finset.subset_univ s)
    intro v _ hv
    have hzero : z.val v = 0 := by_contra fun hn => hv (hsupport v hn)
    rw [hzero, zero_smul]

theorem finiteGeometricEvaluation_surjective
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices]
    (x : E) (hx : x ∈ K.space) : ∃ z, finiteGeometricEvaluation K z = x := by
  classical
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨w, hw, hwsum, hwx⟩ := Finset.mem_convexHull'.mp hxs
  have hsvertices (y : E) (hy : y ∈ s) : y ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty y)
  let t : Finset K.vertices := Finset.univ.filter (fun v => v.val ∈ s)
  have htv (v : K.vertices) : v ∈ t ↔ v.val ∈ s := by simp [t]
  have htimage : t.image Subtype.val = s := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact (htv v).mp hv
    · intro hy
      exact Finset.mem_image.mpr ⟨⟨y, hsvertices y hy⟩, (htv _).mpr hy, rfl⟩
  let z : K.vertices → Real := fun v => if v.val ∈ s then w v.val else 0
  have hzsupport (v : K.vertices) (hv : z v ≠ 0) : v ∈ t := by
    apply (htv v).mpr
    by_contra hvs
    exact hv (if_neg hvs)
  have hzval (v : K.vertices) (hv : v ∈ t) : z v = w v.val := if_pos ((htv v).mp hv)
  have hsum : ∑ v, z v = 1 := by
    calc
      ∑ v, z v = ∑ v ∈ t, z v := by
        apply (Finset.sum_subset (Finset.subset_univ t) _).symm
        intro v _ hv
        exact by_contra fun hn => hv (hzsupport v hn)
      _ = ∑ v ∈ t, w v.val := Finset.sum_congr rfl hzval
      _ = ∑ y ∈ s, w y := by
        rw [← htimage, Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
      _ = 1 := hwsum
  have hz : z ∈ (finiteGeometricCoordinates K).space := by
    apply (finiteGeometricCoordinates_space K z).mpr
    refine ⟨?_, hsum, t, ?_, hzsupport⟩
    · intro v
      dsimp [z]
      split_ifs with hv
      · exact hw v.val hv
      · exact le_refl _
    · rw [htimage]
      exact hs
  refine ⟨⟨z, hz⟩, ?_⟩
  change (∑ v, z v • v.val) = x
  calc
    ∑ v, z v • v.val = ∑ v ∈ t, z v • v.val := by
      apply (Finset.sum_subset (Finset.subset_univ t) _).symm
      intro v _ hv
      have hzero : z v = 0 := by_contra fun hn => hv (hzsupport v hn)
      rw [hzero, zero_smul]
    _ = ∑ v ∈ t, w v.val • v.val :=
      Finset.sum_congr rfl (fun v hv => by rw [hzval v hv])
    _ = ∑ y ∈ s, w y • y := by
      rw [← htimage, Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
    _ = x := hwx

theorem finiteGeometricCoordinates_isCompact
    (K : Geometry.SimplicialComplex Real E) [Finite K.vertices] :
    IsCompact (finiteGeometricCoordinates K).space := by
  let L := finiteGeometricCoordinates K
  let : Finite L.faces := (finiteGeometricCoordinates_finite K).to_subtype
  have hspace : L.space = ⋃ s : L.faces, convexHull Real (s.val : Set (K.vertices → Real)) := by
    ext x
    simp [Geometry.SimplicialComplex.space]
  rw [hspace]
  apply isCompact_iUnion
  intro s
  exact s.val.finite_toSet.isCompact_convexHull Real

noncomputable def finiteGeometricHomeomorph
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices] :
    (finiteGeometricCoordinates K).space ≃ₜ K.space := by
  letI : CompactSpace (finiteGeometricCoordinates K).space :=
    isCompact_iff_compactSpace.mp (finiteGeometricCoordinates_isCompact K)
  let f : (finiteGeometricCoordinates K).space → K.space :=
    fun z => ⟨finiteGeometricEvaluation K z, finiteGeometricEvaluation_mem K z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' h
      exact finiteGeometricEvaluation_injective K (congrArg Subtype.val h)
    · intro x
      obtain ⟨z, hz⟩ := finiteGeometricEvaluation_surjective K x.val x.property
      exact ⟨z, Subtype.ext hz⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    ((finiteGeometricEvaluation K).continuous.subtype_mk _)

theorem finiteGeometricHomeomorph_apply
    (K : Geometry.SimplicialComplex Real E) [Fintype K.vertices]
    (z : (finiteGeometricCoordinates K).space) :
    (finiteGeometricHomeomorph K z).val = ∑ v, z.val v • v.val := rfl

end Poincare.Topology
