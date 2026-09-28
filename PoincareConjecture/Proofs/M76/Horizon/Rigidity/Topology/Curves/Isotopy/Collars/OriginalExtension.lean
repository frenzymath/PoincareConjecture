import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.ClosedExtension



set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

theorem collar_image_relative_frontier_subset_inner
    {E X : Type*} [TopologicalSpace X]
    (A : Set E) {R : Set X} {eps : ℝ} (c : E × ℝ → X)
    (hclosed : IsClosed (c '' (A ×ˢ Icc (0 : ℝ) eps)))
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Ico (0 : ℝ) eps)))) :
    frontier ((Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Icc (0 : ℝ) eps))) ⊆
      (Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ {eps})) := by
  intro x hx
  have hxD : (x : X) ∈ c '' (A ×ˢ Icc (0 : ℝ) eps) :=
    (hclosed.preimage continuous_subtype_val).closure_subset (frontier_subset_closure hx)
  obtain ⟨z, hz, hzx⟩ := hxD
  have heq : z.2 = eps := by
    apply le_antisymm hz.2.2
    by_contra hn
    have hxO : x ∈ (Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Ico (0 : ℝ) eps)) :=
      ⟨z, ⟨hz.1, hz.2.1, lt_of_not_ge hn⟩, hzx⟩
    have hsub : (Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Ico (0 : ℝ) eps)) ⊆
        (Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Icc (0 : ℝ) eps)) := by
      rintro y ⟨w, hw, hwy⟩
      exact ⟨w, ⟨hw.1, hw.2.1, hw.2.2.le⟩, hwy⟩
    have hi : x ∈ interior ((Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Icc (0 : ℝ) eps))) :=
      interior_mono hsub (by rwa [hopen.interior_eq])
    exact hx.2 hi
  exact ⟨z, ⟨hz.1, heq⟩, hzx⟩

def collarImageInRegion {X : Type*} [TopologicalSpace X]
    {D R : Set X} (hDR : D ⊆ R) : D ≃ₜ ((Subtype.val : R → X) ⁻¹' D) where
  toFun x := ⟨⟨x, hDR x.property⟩, x.property⟩
  invFun x := ⟨(x : R), x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem exists_collar_identity_extension
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (A : Set E) {R : Set X} {eps : ℝ} (heps : 0 < eps) (c : E × ℝ → X)
    (hclosed : IsClosed (c '' (A ×ˢ Icc (0 : ℝ) eps)))
    (hDR : c '' (A ×ˢ Icc (0 : ℝ) eps) ⊆ R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (A ×ˢ Ico (0 : ℝ) eps))))
    (C : (A ×ˢ Icc (0 : ℝ) eps) ≃ₜ (c '' (A ×ˢ Icc (0 : ℝ) eps)))
    (hCv : ∀ z, (C z : X) = c z)
    (Q : I → (c '' (A ×ˢ Icc (0 : ℝ) eps)) ≃ₜ (c '' (A ×ˢ Icc (0 : ℝ) eps)))
    (hQ : Continuous (fun z : I × (c '' (A ×ˢ Icc (0 : ℝ) eps)) => Q z.1 z.2))
    (hQi : Continuous (fun z : I × (c '' (A ×ˢ Icc (0 : ℝ) eps)) => (Q z.1).symm z.2))
    (hQzero : Q 0 = Homeomorph.refl _)
    (hinner : ∀ t : I, ∀ x : A,
      Q t (C ⟨(x, eps), x.property, heps.le, le_rfl⟩) =
        C ⟨(x, eps), x.property, heps.le, le_rfl⟩) :
    ∃ G : I → R ≃ₜ R,
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ∀ x : (c '' (A ×ˢ Icc (0 : ℝ) eps)),
        G t ⟨x, hDR x.property⟩ = ⟨Q t x, hDR (Q t x).property⟩) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ c '' (A ×ˢ Icc (0 : ℝ) eps) → G t x = x) := by
  let D := c '' (A ×ˢ Icc (0 : ℝ) eps)
  let T : Set R := (Subtype.val : R → X) ⁻¹' D
  let J : D ≃ₜ T := collarImageInRegion hDR
  let F (t : I) : T ≃ₜ T := J.symm.trans ((Q t).trans J)
  have hT : IsClosed T := hclosed.preimage continuous_subtype_val
  have hfix (t : I) (x : T) (hx : (x : R) ∈ frontier T) : F t x = x := by
    obtain ⟨z, hz, hzx⟩ := collar_image_relative_frontier_subset_inner A c hclosed hopen hx
    have hzeps : z.2 = eps := hz.2
    let a : A := ⟨z.1, hz.1⟩
    let y : (A ×ˢ Icc (0 : ℝ) eps) := ⟨(a, eps), a.property, heps.le, le_rfl⟩
    have hy : C y = J.symm x := by
      apply Subtype.ext
      rw [hCv]
      change c ((z.1), eps) = (x : R)
      simpa only [← hzeps, Prod.eta] using hzx
    have hfx : Q t (J.symm x) = J.symm x := by
      rw [← hy]
      exact hinner t a
    change J (Q t (J.symm x)) = x
    rw [hfx, J.apply_symm_apply]
  let G (t : I) := (F t).closedExtension hT (hfix t)
  have hFc : Continuous (fun z : I × T => F z.1 z.2) := by
    exact J.continuous.comp (f := fun z : I × T => Q z.1 (J.symm z.2))
      (hQ.comp (f := fun z : I × T => (z.1, J.symm z.2))
        (continuous_fst.prodMk (J.symm.continuous.comp continuous_snd)))
  have hFic : Continuous (fun z : I × T => (F z.1).symm z.2) := by
    exact J.continuous.comp (f := fun z : I × T => (Q z.1).symm (J.symm z.2))
      (hQi.comp (f := fun z : I × T => (z.1, J.symm z.2))
        (continuous_fst.prodMk (J.symm.continuous.comp continuous_snd)))
  have hGin (t : I) (x : D) :
      G t ⟨x, hDR x.property⟩ = ⟨Q t x, hDR (Q t x).property⟩ := by
    rw [Homeomorph.closedExtension_apply_mem _ hT _ x.property]
    rfl
  have hGout (t : I) (x : R) (hx : (x : X) ∉ D) : G t x = x :=
    Homeomorph.closedExtension_apply_notMem _ hT _ hx
  refine ⟨G, Homeomorph.continuous_closedExtension_family F hT hFc hfix,
    Homeomorph.continuous_closedExtension_family_symm F hT hFic hfix, ?_, hGin, hGout⟩
  apply Homeomorph.ext
  intro x
  by_cases hx : (x : X) ∈ D
  · have h := hGin 0 ⟨x, hx⟩
    rw [hQzero] at h
    exact h
  · exact hGout 0 x hx

theorem exists_original_collar_region_motion
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} {eps : ℝ} (heps : 0 < eps)
    (c : E × ℝ → X)
    (hcPL : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) eps))
    (hemb : IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) eps) => c z))
    (hmap : MapsTo c (K.space ×ˢ Icc (0 : ℝ) eps) R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) eps))))
    (H : I → K.space ≃ₜ K.space)
    (hc : Continuous (fun z : I × K.space => H z.1 z.2))
    (hci : Continuous (fun z : I × K.space => (H z.1).symm z.2))
    (hzero : ∀ x, H 0 x = x)
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ K.space))
    (hvalue : ∀ t : I, ∀ x : K.space, track ((t : ℝ), x) = (H t x : E)) :
    ∃ G : I → R ≃ₜ R,
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
        (G t ⟨c z, hmap z.property⟩ : X) = c (scaledCollarExtension heps H hc hci t z)) ∧
      (∀ t : I, ∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
        ((G t).symm ⟨c z, hmap z.property⟩ : X) =
          c ((scaledCollarExtension heps H hc hci t).symm z)) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G t x = x) ∧
      (∀ t : I, ∀ x : K.space,
        (G t ⟨c (x, 0), hmap ⟨x.property, le_rfl, heps.le⟩⟩ : X) = c (H t x, 0)) ∧
      (∀ t : I, ∀ x : K.space,
        G t ⟨c (x, eps), hmap ⟨x.property, heps.le, le_rfl⟩⟩ =
          ⟨c (x, eps), hmap ⟨x.property, heps.le, le_rfl⟩⟩) := by
  obtain ⟨C, Q, hCv, _, hD, hQ, hQi, hQzero, hconj, houter, hinner, _⟩ :=
    exists_original_collar_motion e K hK heps c hcPL hemb H hc hci hzero track htrack hvalue
  have hDR : c '' (K.space ×ˢ Icc (0 : ℝ) eps) ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact hmap hz
  obtain ⟨G, hG, hGi, hGzero, hGin, hGout⟩ := exists_collar_identity_extension
    K.space heps c hD hDR hopen C hCv Q hQ hQi hQzero hinner
  have hval (t : I) (z : (K.space ×ˢ Icc (0 : ℝ) eps)) :
      (G t ⟨c z, hmap z.property⟩ : X) = c (scaledCollarExtension heps H hc hci t z) := by
    have h := congrArg Subtype.val (hGin t (C z))
    have hin : (⟨C z, hDR (C z).property⟩ : R) = ⟨c z, hmap z.property⟩ :=
      Subtype.ext (hCv z)
    rw [hin] at h
    exact h.trans ((congrArg Subtype.val (hconj t z)).trans (hCv _))
  refine ⟨G, hG, hGi, hGzero, hval, ?_, hGout, ?_, ?_⟩
  · intro t z
    have h := hval t ((scaledCollarExtension heps H hc hci t).symm z)
    rw [(scaledCollarExtension heps H hc hci t).apply_symm_apply] at h
    have heq : G t ⟨c ((scaledCollarExtension heps H hc hci t).symm z),
        hmap ((scaledCollarExtension heps H hc hci t).symm z).property⟩ =
        ⟨c z, hmap z.property⟩ := Subtype.ext h
    exact congrArg Subtype.val ((G t).symm_apply_eq.mpr heq.symm)
  · intro t x
    rw [hval t ⟨(x, 0), x.property, le_rfl, heps.le⟩,
      scaledCollarExtension_outer]
  · intro t x
    apply Subtype.ext
    rw [hval t ⟨(x, eps), x.property, heps.le, le_rfl⟩,
      scaledCollarExtension_inner heps H hc hci hzero]

end PoincareConjecture.M76.CollarIsotopy
