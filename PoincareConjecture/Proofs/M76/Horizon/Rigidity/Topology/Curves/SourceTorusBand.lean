import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall









set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.PeriodicSquare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ} [Fact (0 < p)]

theorem SourceSquareMap.exists_coordinate_band
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K)
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
      (b : C(AddCircle p × Icc (-r) r, K.space)) (u : (ℝ × ℝ) → E),
      (∀ z : Square p, h (projection p z) = M.map z) ∧
      IsEmbedding b ∧
      (∀ z, b z = h (z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p))) ∧
      IsOpen (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) ∧
      FinitePiecewiseAffineOn u (Icc (0 : ℝ) p ×ˢ Icc (-r) r) ∧
      (∀ s : Icc (0 : ℝ) p, ∀ t : Icc (-r) r,
        u ((s : ℝ), (t : ℝ)) = (b ((s : ℝ), t) : E)) ∧
      ∃ retract : C(K.space, AddCircle p), ∀ z, retract (b z) = z.1 := by
  classical
  obtain ⟨h, hval⟩ := exists_homeomorph_of_sourceSquareMap p M
  obtain ⟨v, hv, hvval⟩ := M.finite_piecewise_affine
  let b : C(AddCircle p × Icc (-r) r, K.space) :=
    ⟨fun z => h (z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p)), by fun_prop⟩
  have hinj : Function.Injective b := by
    intro z w heq
    have hh := h.injective heq
    apply Prod.ext
    · exact congrArg (fun v : AddCircle p × AddCircle p => v.1) hh
    apply Subtype.ext
    have hnormal := congrArg Prod.snd hh
    have hz : p / 2 + (z.2 : ℝ) ∈ Ico (0 : ℝ) p := by
      constructor <;> linarith [z.2.property.1, z.2.property.2]
    have hw : p / 2 + (w.2 : ℝ) ∈ Ico (0 : ℝ) p := by
      constructor <;> linarith [w.2.property.1, w.2.property.2]
    have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show p / 2 + (z.2 : ℝ) ∈ Ico 0 (0 + p) by simpa using hz)
      (show p / 2 + (w.2 : ℝ) ∈ Ico 0 (0 + p) by simpa using hw)).mp hnormal
    linarith
  have hi : IsEmbedding b := (b.continuous.isClosedEmbedding hinj).isEmbedding
  have himage : b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r} =
      h '' (univ ×ˢ (((↑) : ℝ → AddCircle p) '' Ioo (p / 2 - r) (p / 2 + r))) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p)), ?_, rfl⟩
      exact ⟨mem_univ _, p / 2 + (z.2 : ℝ), by constructor <;> linarith [hz.1, hz.2], rfl⟩
    · rintro ⟨⟨s, t⟩, ⟨_, v, hv, rfl⟩, rfl⟩
      let t : Icc (-r) r := ⟨v - p / 2, by constructor <;> linarith [hv.1, hv.2]⟩
      refine ⟨(s, t), ?_, ?_⟩
      · change v - p / 2 ∈ Ioo (-r) r
        constructor <;> linarith [hv.1, hv.2]
      · change h (s, ((p / 2 + (v - p / 2) : ℝ) : AddCircle p)) = h (s, (v : AddCircle p))
        rw [show p / 2 + (v - p / 2) = v by ring]
  have hopen : IsOpen (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) := by
    rw [himage]
    apply h.isOpenMap
    exact isOpen_univ.prod (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)
  let A : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) := ContinuousAffineMap.id ℝ (ℝ × ℝ) +
    ContinuousAffineMap.const ℝ (ℝ × ℝ) (0, p / 2)
  have hA (z : ℝ × ℝ) : A z = (z.1, p / 2 + z.2) := by
    ext <;> simp [A, add_comm]
  have hball := (isFinitePLBallPair_Icc (Fact.out : (0 : ℝ) < p)).prod
    (isFinitePLBallPair_Icc (by linarith : -r < r))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hball
  have ha : FinitePiecewiseAffineOn A (Icc (0 : ℝ) p ×ˢ Icc (-r) r) := by
    rw [← hJs]
    exact (J.affineOnFaces_affine A).finitePiecewiseAffineOn hJ
  have hmap : MapsTo A (Icc (0 : ℝ) p ×ˢ Icc (-r) r) (squareCarrier p) := by
    intro z hz
    rw [hA]
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  refine ⟨h, b, v ∘ A, hval, hi, fun _ => rfl, hopen, hv.comp ha hmap, ?_,
    ⟨fun x => (h.symm x).1, h.symm.continuous.fst⟩, ?_⟩
  · intro s t
    let z : Square p := (s, ⟨p / 2 + (t : ℝ), by
      constructor <;> linarith [t.property.1, t.property.2]⟩)
    change v (A ((s : ℝ), (t : ℝ))) = (h (projection p z) : E)
    rw [hA, hval]
    exact hvval z
  · intro z
    exact congrArg Prod.fst (h.symm_apply_apply _)



theorem SourceSquareMap.exists_original_coordinate_band
    [FiniteDimensional ℝ E]
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : ι → OpenPartialHomeomorph X V}
    {K : SimplicialComplex ℝ E} (M : SourceSquareMap p K)
    {S : Set X} (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ S)
      (b : C(AddCircle p × Icc (-r) r, S)) (f : (ℝ × ℝ) → X),
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      IsEmbedding b ∧
      (∀ z, b z = h (z.1, ((p / 2 + (z.2 : ℝ) : ℝ) : AddCircle p))) ∧
      IsOpen (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) ∧
      PolyhedralPLInCharts e f (Icc (0 : ℝ) p ×ˢ Icc (-r) r) ∧
      (∀ s : Icc (0 : ℝ) p, ∀ t : Icc (-r) r,
        f ((s : ℝ), (t : ℝ)) = (b ((s : ℝ), t) : X)) ∧
      ∃ retract : C(S, AddCircle p), ∀ z, retract (b z) = z.1 := by
  obtain ⟨h, b, u, hval, hi, hb, hopen, hu, huv, R, hR⟩ :=
    M.exists_coordinate_band hr hwidth
  let b' : C(AddCircle p × Icc (-r) r, S) :=
    ⟨fun z => H (b z), H.continuous.comp b.continuous⟩
  have hball := (isFinitePLBallPair_Icc (Fact.out : (0 : ℝ) < p)).prod
    (isFinitePLBallPair_Icc (by linarith : -r < r))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hball
  have humap : MapsTo u (Icc (0 : ℝ) p ×ˢ Icc (-r) r) K.space := by
    intro z hz
    rw [show u z = (b ((z.1 : AddCircle p), ⟨z.2, hz.2⟩) : E) from
      huv ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩]
    exact (b _).property
  have hf : PolyhedralPLInCharts e (F ∘ u)
      (Icc (0 : ℝ) p ×ˢ Icc (-r) r) := by
    rw [← hJs] at hu humap ⊢
    exact hF.comp_finitePiecewiseAffineOn J hJ hu humap
  refine ⟨h.trans H, b', F ∘ u, fun z => congrArg H (hval z), H.isEmbedding.comp hi,
    fun z => congrArg H (hb z), ?_, hf, ?_,
    ⟨fun x => R (H.symm x), R.continuous.comp H.symm.continuous⟩, ?_⟩
  · have him : b' '' {z | (z.2 : ℝ) ∈ Ioo (-r) r} =
        H '' (b '' {z | (z.2 : ℝ) ∈ Ioo (-r) r}) := by
      exact (image_image H b _).symm
    rw [him]
    exact H.isOpenMap _ hopen
  · intro s t
    change F (u ((s : ℝ), (t : ℝ))) = (H (b ((s : ℝ), t)) : X)
    rw [huv]
    exact hFval _
  · intro z
    change R (H.symm (H (b z))) = z.1
    rw [H.symm_apply_apply]
    exact hR z

end PoincareConjecture.M76.PeriodicSquare
