import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineParameterAvoidance
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedVertexDisplacement
import PoincareConjecture.Proofs.M76.Mathlib.SmallSupportedPLIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import Mathlib.Topology.UnitInterval











set_option autoImplicit false

open Set Geometry unitInterval

namespace Geometry.SimplicialComplex






theorem exists_small_protected_vertex_motion
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (J Q : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hcv : Convex ℝ J.space) (hQJ : Q ≤ J)
    (hfront : frontier J.space ⊆ Q.space)
    {v : E} (hv : v ∈ J.vertices) (hvQ : v ∉ Q.vertices)
    (A : ι → AffineSubspace ℝ E) (hA : ∀ i, A i ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : I → E ≃ₜ E,
      Continuous (fun p : I × E => H p.1 p.2) ∧
      Continuous (fun p : I × E => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ t x, x ∉ interior J.space → H t x = x) ∧
      (∀ t x, x ∈ Q.space → H t x = x) ∧
      (∀ t w, w ∈ J.vertices → w ≠ v → H t w = w) ∧
      (∀ t, H t '' J.space = J.space ∧
        ∃ e : J.space ≃ₜ J.space, e.IsFinitePL ∧ ∀ x : J.space, (e x : E) = H t x) ∧
      (∀ t x, dist (H t x) x < ε) ∧
      (∀ i, H 1 v ∉ A i) ∧ ∀ t, J.AffineOnFaces (H t) := by
  obtain ⟨u, hu⟩ := AffineSubspace.exists_avoiding_directions A hA
  obtain ⟨f, hf, hfv, hfw, hfb, hfQ⟩ :=
    J.exists_protected_vertex_displacement Q hQJ hv hvQ u
  have hfzero : ∀ x ∈ frontier J.space, f x = 0 := fun _ hx => hfQ (hfront hx)
  obtain ⟨δ, hδ, G, hGcont, hGinv, hGformula, hGrest⟩ :=
    (hf.finitePiecewiseAffineOn hJ).exists_small_supported_isotopy hcv hfzero
  have hbound : 0 < min δ (ε / (‖u‖ + 1)) :=
    lt_min hδ (div_pos hε (by positivity))
  obtain ⟨a, ha, havoid⟩ := AffineSubspace.exists_pos_small_line_avoiding A v u hu hbound
  have haδ : a ≤ δ := ha.2.le.trans (min_le_left _ _)
  have haε : a * (‖u‖ + 1) < ε :=
    (lt_div_iff₀ (by positivity)).mp (ha.2.trans_le (min_le_right _ _))
  have hanorm : a * ‖u‖ < ε := by nlinarith [ha.1]
  have htime (t : I) : 0 ≤ (t : ℝ) * a ∧ (t : ℝ) * a ≤ a := by
    constructor
    · exact mul_nonneg t.property.1 ha.1.le
    · nlinarith [t.property.2, ha.1]
  let θ : I → Icc (-δ) δ := fun t =>
    ⟨(t : ℝ) * a, ⟨(neg_nonpos.mpr hδ.le).trans (htime t).1,
      (htime t).2.trans haδ⟩⟩
  have hθ : Continuous θ :=
    (continuous_subtype_val.mul continuous_const).subtype_mk _
  let H : I → E ≃ₜ E := fun t => G (θ t)
  have hformula (t : I) (x : E) (hx : x ∈ J.space) :
      H t x = x + ((t : ℝ) * a) • f x := by
    simpa only [H, θ, indicator_of_mem hx] using hGformula (θ t) x
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hGcont.comp ((hθ.comp continuous_fst).prodMk continuous_snd)
  · exact hGinv.comp ((hθ.comp continuous_fst).prodMk continuous_snd)
  · intro x
    change G (θ 0) x = x
    rw [hGformula]
    change x + ((0 : ℝ) * a) • J.space.indicator f x = x
    simp only [zero_mul, zero_smul, add_zero]
  · intro t x hx
    exact (hGrest (θ t)).1 x hx
  · intro t x hx
    rw [hformula t x (space_subset_of_le hQJ hx), hfQ hx, smul_zero, add_zero]
  · intro t w hw hwv
    rw [hformula t w (J.vertices_subset_space hw), hfw w hw hwv, smul_zero, add_zero]
  · intro t
    exact (hGrest (θ t)).2
  · intro t x
    by_cases hx : x ∈ J.space
    · rw [hformula t x hx, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (htime t).1]
      exact ((mul_le_mul_of_nonneg_left (hfb x hx) (htime t).1).trans
        (mul_le_mul_of_nonneg_right (htime t).2 (norm_nonneg u))).trans_lt hanorm
    · have hfix : H t x = x :=
        (hGrest (θ t)).1 x (fun hi => hx (interior_subset hi))
      rw [hfix, dist_self]
      exact hε
  · intro i
    have hval : H 1 v = v + a • u := by
      simpa only [Set.Icc.coe_one, one_mul, hfv] using
        hformula 1 v (J.vertices_subset_space hv)
    rw [hval]
    exact havoid i
  · intro t s hs
    obtain ⟨b, hb⟩ := hf s hs
    refine ⟨ContinuousAffineMap.id ℝ E + ((t : ℝ) * a) • b, ?_⟩
    intro x hx
    change H t x = x + ((t : ℝ) * a) • b x
    rw [hformula t x (J.convexHull_subset_space hs hx), hb hx]

end Geometry.SimplicialComplex
