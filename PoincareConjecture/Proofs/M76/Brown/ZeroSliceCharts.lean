import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas









set_option autoImplicit false

open Set

namespace BrownCollar

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]




noncomputable def zeroSliceHomeomorph
    (e : OpenPartialHomeomorph X (P × ℝ)) (S : Set X)
    (hpair : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) :
    ↥((Subtype.val : S → X) ⁻¹' e.source) ≃ₜ
      ↥((fun p : P => (p, (0 : ℝ))) ⁻¹' e.target) := by
  let W := (Subtype.val : S → X) ⁻¹' e.source
  let T := (fun p : P => (p, (0 : ℝ))) ⁻¹' e.target
  have hzero (z : W) : (e (z.val : X)).2 = 0 :=
    (hpair _ z.property).mp z.val.property
  have hcoord (z : W) : ((e (z.val : X)).1, (0 : ℝ)) = e (z.val : X) :=
    Prod.ext rfl (hzero z).symm
  have hinv (p : T) : e.symm (p.val, 0) ∈ S := by
    apply (hpair _ (e.map_target p.property)).mpr
    rw [e.right_inv p.property]
  refine
    { toFun := fun z => ⟨(e (z.val : X)).1, by
        change ((e (z.val : X)).1, (0 : ℝ)) ∈ e.target
        rw [hcoord z]
        exact e.map_source z.property⟩
      invFun := fun p => ⟨⟨e.symm (p.val, 0), hinv p⟩, e.map_target p.property⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change e.symm ((e (z.val : X)).1, 0) = (z.val : X)
    rw [hcoord z]
    exact e.left_inv z.property
  · intro p
    apply Subtype.ext
    exact congrArg Prod.fst (e.right_inv p.property)
  · apply Continuous.subtype_mk
    exact continuous_fst.comp (e.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.property))
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact e.symm.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun p => p.property)




theorem exists_zeroSliceChart
    (e : OpenPartialHomeomorph X (P × ℝ)) (S : Set X)
    (hpair : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : S) (hx : (x : X) ∈ e.source) :
    ∃ phi : OpenPartialHomeomorph S P,
      phi.source = (Subtype.val : S → X) ⁻¹' e.source ∧
      phi.target = (fun p : P => (p, (0 : ℝ))) ⁻¹' e.target ∧
      ∀ s ∈ phi.source, phi s = (e (s : X)).1 := by
  let W : TopologicalSpace.Opens S :=
    ⟨(Subtype.val : S → X) ⁻¹' e.source, e.open_source.preimage continuous_subtype_val⟩
  let T : TopologicalSpace.Opens P :=
    ⟨(fun p : P => (p, (0 : ℝ))) ⁻¹' e.target,
      e.open_target.preimage (continuous_id.prodMk continuous_const)⟩
  let f : W ≃ₜ T := zeroSliceHomeomorph e S hpair
  let w0 : W := ⟨x, hx⟩
  let iw := W.openPartialHomeomorphSubtypeCoe ⟨w0⟩
  let it := T.openPartialHomeomorphSubtypeCoe ⟨f w0⟩
  have hiwS : iw.source = univ := rfl
  have hiwT : iw.target = (W : Set S) := W.openPartialHomeomorphSubtypeCoe_target ⟨w0⟩
  have hitS : it.source = univ := rfl
  have hitT : it.target = (T : Set P) := T.openPartialHomeomorphSubtypeCoe_target ⟨f w0⟩
  let phi := iw.symm.trans (f.toOpenPartialHomeomorph.trans it)
  have hphiS : phi.source = (Subtype.val : S → X) ⁻¹' e.source := by
    dsimp only [phi]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, hitS, preimage_univ, inter_univ, hiwT]
    rfl
  have hphiT : phi.target = (fun p : P => (p, (0 : ℝ))) ⁻¹' e.target := by
    dsimp only [phi]
    simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Homeomorph.toOpenPartialHomeomorph_target, hiwS, preimage_univ, inter_univ, hitT]
    rfl
  refine ⟨phi, hphiS, hphiT, ?_⟩
  intro s hs
  let w : W := ⟨s, by
    change s ∈ (Subtype.val : S → X) ⁻¹' e.source
    rw [← hphiS]
    exact hs⟩
  have hiwinv : iw.symm s = w := iw.left_inv (x := w) (mem_univ w)
  change (f (iw.symm s) : P) = (e (s : X)).1
  rw [hiwinv]
  rfl





theorem exists_local_pair_chart
    (e : OpenPartialHomeomorph X (P × ℝ)) (S : Set X)
    (hpair : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : S) (hx : (x : X) ∈ e.source) :
    ∃ q : OpenPartialHomeomorph (S × ℝ) X,
      (x, (0 : ℝ)) ∈ q.source ∧
      (∀ s, (s, (0 : ℝ)) ∈ q.source → q (s, 0) = (s : X)) ∧
      ∀ z ∈ q.source, q z ∈ S ↔ z.2 = 0 := by
  obtain ⟨phi, hphiS, _, hformula⟩ := exists_zeroSliceChart e S hpair x hx
  let q := (phi.prod (OpenPartialHomeomorph.refl ℝ)).trans e.symm
  have hcoord (s : S) (hs : s ∈ phi.source) :
      (phi s, (0 : ℝ)) = e (s : X) := by
    apply Prod.ext
    · exact hformula s hs
    · have hsA : (s : X) ∈ e.source := by
        simpa only [hphiS, mem_preimage] using hs
      exact ((hpair _ hsA).mp s.property).symm
  have hxphi : x ∈ phi.source := by
    rw [hphiS]
    exact hx
  refine ⟨q, ?_, ?_, ?_⟩
  · refine ⟨⟨hxphi, mem_univ _⟩, ?_⟩
    change (phi x, (0 : ℝ)) ∈ e.target
    rw [hcoord x hxphi]
    exact e.map_source hx
  · intro s hs
    change e.symm (phi s, (0 : ℝ)) = (s : X)
    rw [hcoord s hs.1.1]
    apply e.left_inv
    simpa only [hphiS, mem_preimage] using hs.1.1
  · intro z hz
    change e.symm (phi z.1, z.2) ∈ S ↔ z.2 = 0
    exact (hpair _ (e.map_target hz.2)).trans (by
      rw [e.right_inv hz.2]
      rfl)

end BrownCollar
