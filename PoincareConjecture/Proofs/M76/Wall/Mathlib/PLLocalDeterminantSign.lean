import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLTransitionSignComparison
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.LocallyConstant.Basic












set_option autoImplicit false

open Set Metric

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




def IsPLAffineWitness (h : OpenPartialHomeomorph E E) (x : E) (A : E →ᴬ[ℝ] E) : Prop :=
  ∃ K : SimplicialComplex ℝ E,
    K.faces.Finite ∧ x ∈ interior K.space ∧ K.space ⊆ h.source ∧
    K.AffineOnFaces h ∧ ∃ t ∈ K.faces,
      t.card = Module.finrank ℝ E + 1 ∧ x ∈ convexHull ℝ (t : Set E) ∧
        EqOn h A (convexHull ℝ (t : Set E))




theorem exists_plAffineWitness (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) {x : E} (hx : x ∈ h.source) :
    ∃ A : E →ᴬ[ℝ] E, IsPLAffineWitness h x A := by
  obtain ⟨K, hK, hxK, hsource, hf, _, _⟩ :=
    exists_finite_paired_facet_orientation h hh hx
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_interior hK hxK
  obtain ⟨A, hA⟩ := hf t ht
  exact ⟨A, K, hK, hxK, hsource, hf, t, ht, htc, hxt, hA⟩




theorem IsPLAffineWitness.det_mul_pos_of_eqOn
    {h g : OpenPartialHomeomorph E E} {x : E} {A B : E →ᴬ[ℝ] E}
    (hA : IsPLAffineWitness h x A) (hB : IsPLAffineWitness g x B)
    {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) (heq : EqOn h g U) :
    LinearMap.det A.toAffineMap.linear ≠ 0 ∧
      LinearMap.det B.toAffineMap.linear ≠ 0 ∧
      0 < LinearMap.det A.toAffineMap.linear * LinearMap.det B.toAffineMap.linear := by
  obtain ⟨K, hK, hxK, hKs, hf, t, ht, htc, hxt, htA⟩ := hA
  obtain ⟨L, hL, hxL, hLs, hg, u, hu, huc, hxu, huB⟩ := hB
  have hnb : U ∩ (interior K.space ∩ interior L.space) ∈ nhds x :=
    (hU.inter (isOpen_interior.inter isOpen_interior)).mem_nhds ⟨hxU, hxK, hxL⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnb
  have hbK : ball x r ⊆ K.space := fun _ hy => interior_subset (hball hy).2.1
  have hbL : ball x r ⊆ L.space := fun _ hy => interior_subset (hball hy).2.2
  exact hf.det_mul_pos_of_eqOn_convex_open hg (h.injOn.mono hKs)
    (g.injOn.mono hLs) hK hL isOpen_ball (convex_ball x r)
    ⟨x, mem_ball_self hr⟩ hbK hbL (fun _ hy => heq (hball hy).1)
    ⟨t, ht, htc, x, hxt, mem_ball_self hr⟩
    ⟨u, hu, huc, x, hxu, mem_ball_self hr⟩ A B htA huB

private theorem sign_eq_of_mul_pos {a b : ℝ} (h : 0 < a * b) :
    SignType.sign a = SignType.sign b := by
  rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [sign_pos ha, sign_pos hb]
  · rw [sign_neg ha, sign_neg hb]




noncomputable def plLocalSign (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) (x : h.source) : SignType :=
  SignType.sign (LinearMap.det
    (Classical.choose (exists_plAffineWitness h hh x.property)).toAffineMap.linear)




theorem plLocalSign_eq_of_witness (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) (x : h.source) {A : E →ᴬ[ℝ] E}
    (hA : IsPLAffineWitness h x A) :
    plLocalSign h hh x = SignType.sign (LinearMap.det A.toAffineMap.linear) := by
  have hc := Classical.choose_spec (exists_plAffineWitness h hh x.property)
  have hp := hc.det_mul_pos_of_eqOn hA isOpen_univ (mem_univ _) (fun _ _ => rfl)
  exact sign_eq_of_mul_pos hp.2.2



theorem plLocalSign_ne_zero (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) (x : h.source) :
    plLocalSign h hh x ≠ 0 := by
  have hc := Classical.choose_spec (exists_plAffineWitness h hh x.property)
  have hp := hc.det_mul_pos_of_eqOn hc isOpen_univ (mem_univ _) (fun _ _ => rfl)
  exact sign_ne_zero.mpr hp.1




theorem plLocalSign_eq_of_eqOn
    (h g : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (hg : g ∈ piecewiseAffineGroupoid E) {x : E}
    (hx : x ∈ h.source) (hxg : x ∈ g.source)
    {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) (heq : EqOn h g U) :
    plLocalSign h hh ⟨x, hx⟩ = plLocalSign g hg ⟨x, hxg⟩ := by
  obtain ⟨A, hA⟩ := exists_plAffineWitness h hh hx
  obtain ⟨B, hB⟩ := exists_plAffineWitness g hg hxg
  rw [plLocalSign_eq_of_witness h hh _ hA, plLocalSign_eq_of_witness g hg _ hB]
  exact sign_eq_of_mul_pos (hA.det_mul_pos_of_eqOn hB hU hxU heq).2.2




theorem plLocalSign_eq_of_active_face
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hKs : K.space ⊆ h.source) (hf : K.AffineOnFaces h)
    {U : Set E} (hU : IsOpen U) (hcv : Convex ℝ U) (hUK : U ⊆ K.space)
    (x : h.source) (hxU : (x : E) ∈ U) (t : K.FullFaceIn U) (A : E →ᴬ[ℝ] E)
    (hA : EqOn h A (convexHull ℝ (t.val : Set E))) :
    plLocalSign h hh x = SignType.sign (LinearMap.det A.toAffineMap.linear) := by
  have hxK : (x : E) ∈ interior K.space :=
    interior_mono hUK (by simpa only [hU.interior_eq] using hxU)
  obtain ⟨u, hu, huc, hxu⟩ := K.exists_full_face_of_mem_interior hK hxK
  obtain ⟨B, hB⟩ := hf u hu
  have hw : IsPLAffineWitness h x B :=
    ⟨K, hK, hxK, hKs, hf, u, hu, huc, hxu, hB⟩
  rw [plLocalSign_eq_of_witness h hh x hw]
  exact sign_eq_of_mul_pos
    (hf.det_mul_pos_on_convex_open (h.injOn.mono hKs) hK hU hcv ⟨x, hxU⟩ hUK
      ⟨u, hu, huc, x, hxu, hxU⟩ t B A hB hA).2.2




theorem isLocallyConstant_plLocalSign (h : OpenPartialHomeomorph E E)
    (hh : h ∈ piecewiseAffineGroupoid E) : IsLocallyConstant (plLocalSign h hh) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨K, hK, hxK, hKs, hf, _, r, hr, hball, _⟩ :=
    exists_finite_convex_sign_neighborhood h hh x.property
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_interior hK hxK
  obtain ⟨A, hA⟩ := hf t ht
  let v : K.FullFaceIn (ball (x : E) r) := ⟨t, ht, htc, x, hxt, mem_ball_self hr⟩
  refine ⟨(Subtype.val : h.source → E) ⁻¹' ball (x : E) r,
    isOpen_ball.preimage continuous_subtype_val, mem_ball_self hr, ?_⟩
  intro y hy
  exact (plLocalSign_eq_of_active_face h hh K hK hKs hf isOpen_ball
    (convex_ball (x : E) r) hball y hy v A hA).trans
      (plLocalSign_eq_of_active_face h hh K hK hKs hf isOpen_ball
        (convex_ball (x : E) r) hball x (mem_ball_self hr) v A hA).symm



theorem plLocalSign_refl (x : (OpenPartialHomeomorph.refl E).source) :
    plLocalSign (OpenPartialHomeomorph.refl E) (piecewiseAffineGroupoid E).id_mem x = 1 := by
  obtain ⟨A, K, hK, hxK, hKs, hf, t, ht, htc, hxt, _⟩ :=
    exists_plAffineWitness (OpenPartialHomeomorph.refl E)
      (piecewiseAffineGroupoid E).id_mem x.property
  have hw : IsPLAffineWitness (OpenPartialHomeomorph.refl E) x
      (ContinuousAffineMap.id ℝ E) :=
    ⟨K, hK, hxK, hKs, hf, t, ht, htc, hxt, fun _ _ => rfl⟩
  rw [plLocalSign_eq_of_witness _ _ _ hw]
  change SignType.sign (LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)) = 1
  simp

end Geometry
