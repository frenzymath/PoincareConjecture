import PoincareConjecture.Proofs.M76.Mathlib.ParametricCorePasting
import PoincareConjecture.Proofs.M76.Mathlib.NormalizedFieldExtension

set_option autoImplicit false

open Set Filter ContinuousLinearMap ContinuousMap
open scoped Topology ContDiff

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem Continuous.exists_frameTransverse_parametric_coreExtension
    {f : X × Y → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ z, Function.RightInverse J (f z))
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    {P : Set Y} (hP : IsCompact P) (A : Set E)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A}]
    (hfront : ∀ x ∈ frontier C, ∀ p ∈ P, (f (x, p)).ker.IsSecantTransverse A) :
    ∃ g : C(X × Y, E →L[ℝ] F), (∀ z, Function.RightInverse J (g z)) ∧
      (g : X × Y → E →L[ℝ] F) =ᶠ[𝓝ˢ ((interior C)ᶜ ×ˢ interior P)] f ∧
      ∀ z ∈ C ×ˢ P, (g z).ker.IsSecantTransverse A := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let T : Set (E →L[ℝ] F) :=
    {Q | Function.RightInverse J Q ∧ Q.ker.IsSecantTransverse A}
  let : ContractibleSpace T :=
    inferInstanceAs (ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A})
  let fP : C(X × P, E →L[ℝ] F) :=
    ⟨fun z => f (z.1, z.2), hf.comp (continuous_id.prodMap continuous_subtype_val)⟩
  let W : Set (E →L[ℝ] F) :=
    {Q | (frameNormalize J (f (0, 0)) Q).ker.IsSecantTransverse A}
  have hW : IsOpen W := isOpen_frameNormalize_transverse J (f (0, 0)) (hframe (0, 0)) A
  have hWeq (z : X × Y) : f z ∈ W ↔ (f z).ker.IsSecantTransverse A := by
    change (frameNormalize J (f (0, 0)) (f z)).ker.IsSecantTransverse A ↔ _
    rw [frameNormalize_eq_self J (f (0, 0)) (f z) (hframe z)]
  let U : Set X := fP.curry ⁻¹' {q : C(P, E →L[ℝ] F) | MapsTo q univ W}
  have hU : IsOpen U := (isOpen_setOfPred_mapsTo isCompact_univ hW).preimage fP.curry.continuous
  have hCU : frontier C ⊆ U := by
    intro x hx p _
    exact (hWeq (x, p)).mpr (hfront x hx p p.property)
  obtain ⟨g, heq, hgt⟩ := fP.exists_parametric_convexCore_replacement_near_compl
    hC hc hi hU hCU T (fun x hx p =>
      ⟨hframe (x, p), (hWeq (x, p)).mp (hx.2 (mem_univ p))⟩)
  have hgn (z : X × P) : Function.RightInverse J (g z) := by
    by_cases hx : z.1 ∈ C
    · exact (hgt z.1 hx z.2).1
    · rw [show g z = fP z from
        heq.self_of_nhdsSet z.1 (fun hxi => hx (interior_subset hxi)) z.2]
      exact hframe (z.1, z.2)
  let D : Set (X × Y) := univ ×ˢ P
  have hD : IsClosed D := isClosed_univ.prod hP.isClosed
  let k : D → X × P := fun z => (z.1.1, ⟨z.1.2, z.2.2⟩)
  have hk : Continuous k :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  let gD : C(D, E →L[ℝ] F) := g.comp ⟨k, hk⟩
  obtain ⟨G, hGn, hGeq⟩ := gD.exists_frame_extension hD J (f (0, 0)) (hframe (0, 0))
    (fun z => hgn (k z))
  have hGvalue (x : X) (p : P) : G (x, (p : Y)) = g (x, p) :=
    hGeq ⟨(x, (p : Y)), mem_univ x, p.property⟩
  obtain ⟨O, hO, hCO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp heq
  have hOS : O ×ˢ interior P ∈ 𝓝ˢ ((interior C)ᶜ ×ˢ interior P) :=
    (hO.prod isOpen_interior).mem_nhdsSet.mpr (prod_mono hCO Subset.rfl)
  refine ⟨G, hGn, ?_, ?_⟩
  · filter_upwards [hOS] with z hz
    rw [hGvalue z.1 ⟨z.2, interior_subset hz.2⟩]
    exact hOeq z.1 hz.1 ⟨z.2, interior_subset hz.2⟩
  · intro z hz
    rw [hGvalue z.1 ⟨z.2, hz.2⟩]
    exact (hgt z.1 hz.1 ⟨z.2, hz.2⟩).2
